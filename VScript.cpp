// ============================================================================
//  VScript.asi  -  a tiny scripting language for GTA Vice City (1.0, x86)
//  Build: 32-bit (x86) DLL, C++11 or newer, rename output to VScript.asi
//  Game folder layout:  VScript\main.vscript   (+ optional VScript\VScript.ini)
//
//  LANGUAGE (one statement per line, '#' or '//' = comment, names are
//  case-insensitive, numbers can be 10, 1.5 or 0xA10A2E)
//
//    x = 5                  x += 1   -= *= /=         (variables, global)
//    x = (a + b) * 2 % 3    == != < > <= >=  && || !   (expressions)
//
//    on start { }           runs once when the script loads
//    every 500 { }          runs every 500 ms
//    key ctrl+F5 { }        runs when the key is pressed (game window only)
//    when int(0x1234) > 5 { }   runs each time the condition turns true
//    func name(a, b) { }    x = name(1, 2)    run name      (reusable blocks; parameters are
//                           global variables; "return expr" gives the value, no return = 0)
//
//    if cond { } else if cond { } else { }
//    while cond { }     repeat 10 { }     break   return   wait 100
//    stop  = end this trigger run          exit = end the whole script
//
//    poke int|short|byte|float ADDR, value      (write memory)
//    nop ADDR, count          patch ADDR, 0x90, 0x90, ...
//    print "text", value, ... (also: log, alert)   -> VScript\vscript.log
//    include "other.vscript"
//
//  FUNCTIONS (use inside expressions):
//    int(a) uint(a) short(a) ushort(a) byte(a) float(a)   read memory
//    ptr(base, off1, off2, ...)       follow a pointer chain, returns address
//    call(addr, args...)              call a cdecl game function (max 6 args)
//    thiscall(addr, this, args...)    call a __thiscall method (max 5 args)
//    fbits(1.5) / bitsf(n)            float <-> raw int bits (for call args)
//    hour() minute() setweather(n)    VC 1.0 clock / weather helpers
//    built-in address variables: new_weather old_weather weather_interp
//      clock_hours clock_minutes players player_in_focus
//    rand(a,b) time() down(key_f5) abs min max floor ceil sqrt sin cos
//    key_<name> gives a key code, e.g. key_a key_f5 key_space
//
//  OTHER PLUGINS (e.g. NewRain.asi) can add commands/functions:
//    typedef double (*VSNative)(int argc, const double* argv);
//    HMODULE m = GetModuleHandleA("VScript.asi");
//    auto reg = (void(*)(const char*, VSNative))GetProcAddress(m,"VScript_Register");
//    reg("drop", MyDrop);        // script:  drop 5, 10     or   x = drop(5)
//  THREADING: scripts run on helper threads, but every memory write, patch, game call
//  and native call is queued and executed on the game's own thread (between frames,
//  through a window-procedure hook, installed only on a window owned by the process' main
//  thread). Reads are direct but range/permission checked. VScript_Shutdown() stops everything
//  and restores the window procedure. Pump() can be called from any real per-frame hook instead.
// ============================================================================
#define WIN32_LEAN_AND_MEAN
#define NOMINMAX                 // windows.h min/max macros would break std::min/std::max
#include <windows.h>
#include <tlhelp32.h>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <memory>
#include <thread>
#include <atomic>
#include <mutex>
#include <fstream>
#include <functional>
#include <deque>
#include <condition_variable>
#include <chrono>
#include <algorithm>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <cctype>
#include <stdexcept>

#ifdef _WIN64
#error "Vice City is a 32-bit game: build this as x86 (Win32)."
#endif

typedef double (*VSNative)(int argc, const double* argv);

// ----------------------------------------------------------------- globals
static std::string g_dir;                 // game folder (with trailing slash)
static std::mutex g_logMx;
static std::map<std::string, VSNative> g_natives;
static std::mutex g_nativeMx;
static std::atomic<int> g_threads(0);      // live script/scheduler/loader threads (for VScript_Shutdown)
static std::atomic<bool> g_quit(false);
static std::mutex g_curMx;
static std::shared_ptr<struct Program> g_cur;   // currently running program

static std::string S(long v) { char b[32]; snprintf(b, sizeof b, "%ld", v); return b; }

static std::string Lower(std::string s) {
    for (size_t i = 0; i < s.size(); ++i) s[i] = (char)tolower((unsigned char)s[i]);
    return s;
}

static void Log(const std::string& s) {
    std::lock_guard<std::mutex> l(g_logMx);
    std::ofstream f((g_dir + "VScript\\vscript.log").c_str(), std::ios::app);
    f << "[" << GetTickCount() << "] " << s << "\n";
    OutputDebugStringA((s + "\n").c_str());
}

// ------------------------------------------------------------------ memory
static bool ProtOk(DWORD p, bool write) {
    if (p & (PAGE_NOACCESS | PAGE_GUARD)) return false;
    if (write) return true;                      // protection is changed before writing
    return (p & (PAGE_READONLY | PAGE_READWRITE | PAGE_WRITECOPY | PAGE_EXECUTE_READ |
                 PAGE_EXECUTE_READWRITE | PAGE_EXECUTE_WRITECOPY)) != 0;
}
// Every page of [a, a+n) must be committed and accessible (walks all regions it spans).
static bool CheckRange(uintptr_t a, size_t n, bool write) {
    if (!a || !n || a + n < a) return false;     // null, empty, or address-space wrap-around
    uintptr_t cur = a, end = a + n;
    while (cur < end) {
        MEMORY_BASIC_INFORMATION m;
        if (!VirtualQuery((const void*)cur, &m, sizeof m)) return false;
        if (m.State != MEM_COMMIT || !ProtOk(m.Protect, write)) return false;
        uintptr_t next = (uintptr_t)m.BaseAddress + m.RegionSize;
        if (next <= cur) return false;
        cur = next;
    }
    return true;
}
static bool Peek(uintptr_t a, void* out, size_t n) {
    if (!CheckRange(a, n, false)) return false;
    memcpy(out, (const void*)a, n);
    return true;
}
// Transactional: phase 1 makes every region writable (and undoes everything if one fails),
// phase 2 copies (nothing left that can fail), phase 3 always restores the old protections.
static bool Poke(uintptr_t a, const void* src, size_t n) {
    if (!CheckRange(a, n, true)) return false;
    struct Seg { uintptr_t at; size_t len; DWORD old; };
    std::vector<Seg> segs; uintptr_t cur = a, end = a + n; bool ok = true;
    while (cur < end) {
        MEMORY_BASIC_INFORMATION m;
        if (!VirtualQuery((const void*)cur, &m, sizeof m)) { ok = false; break; }
        uintptr_t next = std::min(end, (uintptr_t)m.BaseAddress + m.RegionSize);
        Seg sg; sg.at = cur; sg.len = next - cur; sg.old = 0;
        if (!VirtualProtect((void*)cur, sg.len, PAGE_EXECUTE_READWRITE, &sg.old)) { ok = false; break; }
        segs.push_back(sg); cur = next;
    }
    if (ok) { memcpy((void*)a, src, n); FlushInstructionCache(GetCurrentProcess(), (void*)a, n); }
    for (size_t i = 0; i < segs.size(); ++i) { DWORD t; VirtualProtect((void*)segs[i].at, segs[i].len, segs[i].old, &t); }
    return ok;
}

// ------------------------------------------- run game-touching work on the game thread
// Script threads never write memory or call game code themselves. They queue the job and
// wait. The queue is drained by a window-procedure hook, i.e. on the game's own thread,
// between frames. If the hook could not be installed, jobs run directly (and a warning is logged).
struct Job {
    std::function<void()> fn; std::mutex m; std::condition_variable cv;
    bool done = false, cancelled = false; std::string err;
};
static std::mutex g_qMx;
static std::condition_variable g_qCv;
static std::deque<std::shared_ptr<Job> > g_queue;
static std::atomic<DWORD> g_mainTid(0);
static std::atomic<bool> g_pumpOn(false);

static void RunOnMain(const std::function<void()>& fn) {
    if (!g_pumpOn || GetCurrentThreadId() == g_mainTid) { fn(); return; }
    std::shared_ptr<Job> j = std::make_shared<Job>(); j->fn = fn;
    { std::lock_guard<std::mutex> l(g_qMx); g_queue.push_back(j); }
    g_qCv.notify_one();
    std::unique_lock<std::mutex> l(j->m);
    // Pump() holds j->m for the whole time the job runs, so when this wait times out and re-takes
    // the lock, a job that already started has finished (done == true -> no timeout is reported).
    // A timeout therefore always means "never started"; it is then cancelled and will be skipped.
    if (!j->cv.wait_for(l, std::chrono::milliseconds(1000), [&] { return j->done; })) {
        j->cancelled = true;
        throw std::runtime_error("game thread did not respond (operation cancelled)");
    }
    if (!j->err.empty()) throw std::runtime_error(j->err);
}

static void Pump() {                              // called on the game thread only
    DWORD start = GetTickCount(); int count = 0; bool ran = false;
    for (;;) {
        std::shared_ptr<Job> j;
        {
            std::unique_lock<std::mutex> l(g_qMx);
            if (g_queue.empty() && ran)           // a running script usually queues its next op at once
                g_qCv.wait_for(l, std::chrono::milliseconds(1), [] { return !g_queue.empty(); });
            if (g_queue.empty()) break;
            j = g_queue.front(); g_queue.pop_front();
        }
        {
            std::lock_guard<std::mutex> l(j->m);
            if (!j->cancelled) {
                try { j->fn(); } catch (std::exception& e) { j->err = e.what(); }
                j->done = true;
            }
        }
        j->cv.notify_all(); ran = true;
        if (++count >= 64 || GetTickCount() - start >= 8) break;   // never hog the frame
    }
}

#define WM_VS_INIT (WM_USER + 0x5653)
#define WM_VS_EXIT (WM_USER + 0x5654)
static const UINT_PTR VS_TIMER = 0x5653;
static WNDPROC g_oldProc = 0;
static bool g_uni = false;
static HWND g_hwnd = NULL;

static LRESULT CALLBACK HookProc(HWND h, UINT m, WPARAM w, LPARAM l) {
    if (m == WM_VS_INIT) { SetTimer(h, VS_TIMER, 5, NULL); return 0; }   // a timer must be made by the window's own thread
    if (m == WM_VS_EXIT) {                                              // runs on the window's thread
        KillTimer(h, VS_TIMER);
        LONG_PTR cur = g_uni ? GetWindowLongPtrW(h, GWLP_WNDPROC) : GetWindowLongPtrA(h, GWLP_WNDPROC);
        if (cur == (LONG_PTR)HookProc) {                                // only unhook if nobody subclassed on top of us
            if (g_uni) SetWindowLongPtrW(h, GWLP_WNDPROC, (LONG_PTR)g_oldProc);
            else       SetWindowLongPtrA(h, GWLP_WNDPROC, (LONG_PTR)g_oldProc);
        }                                                               // else stay as a pass-through (module is pinned)
        g_pumpOn = false; return 0;
    }
    Pump();
    return g_uni ? CallWindowProcW(g_oldProc, h, m, w, l) : CallWindowProcA(g_oldProc, h, m, w, l);
}

// The process' main thread = the thread that was created first (it runs WinMain / the game loop).
static DWORD ProcessMainThreadId() {
    DWORD pid = GetCurrentProcessId(), best = 0; ULONGLONG bestT = ~0ULL;
    HANDLE snap = CreateToolhelp32Snapshot(TH32CS_SNAPTHREAD, 0);
    if (snap == INVALID_HANDLE_VALUE) return 0;
    THREADENTRY32 te; te.dwSize = sizeof te;
    for (BOOL ok = Thread32First(snap, &te); ok; ok = Thread32Next(snap, &te)) {
        if (te.th32OwnerProcessID != pid) continue;
        HANDLE th = OpenThread(THREAD_QUERY_INFORMATION, FALSE, te.th32ThreadID);
        if (!th) continue;
        FILETIME c, e, k, u;
        if (GetThreadTimes(th, &c, &e, &k, &u)) {
            ULONGLONG t = ((ULONGLONG)c.dwHighDateTime << 32) | c.dwLowDateTime;
            if (t < bestT) { bestT = t; best = te.th32ThreadID; }
        }
        CloseHandle(th);
    }
    CloseHandle(snap);
    return best;
}

struct WinSearch { DWORD mainTid; HWND found; DWORD otherTid; };
static BOOL CALLBACK FindGameWnd(HWND h, LPARAM p) {
    WinSearch* s = (WinSearch*)p; DWORD pid = 0;
    DWORD tid = GetWindowThreadProcessId(h, &pid);
    if (pid != GetCurrentProcessId() || !IsWindowVisible(h) || GetWindow(h, GW_OWNER)) return TRUE;
    if (tid == s->mainTid) { s->found = h; return FALSE; }     // only accept a window owned by the main thread
    s->otherTid = tid; return TRUE;
}
// 1 = installed, 0 = window not there yet (retry), -1 = refused (not safe to hook)
static int InstallHook() {
    DWORD mainTid = ProcessMainThreadId();
    if (!mainTid) { Log("pump: could not determine the main thread"); return -1; }
    WinSearch s; s.mainTid = mainTid; s.found = NULL; s.otherTid = 0;
    EnumWindows(FindGameWnd, (LPARAM)&s);
    if (!s.found) {
        if (s.otherTid) { Log("pump refused: game window belongs to thread " + S((long)s.otherTid) +
                              ", main thread is " + S((long)mainTid)); return -1; }
        return 0;
    }
    HWND h = s.found;
    g_uni = IsWindowUnicode(h) != 0;
    WNDPROC prev = (WNDPROC)(g_uni ? GetWindowLongPtrW(h, GWLP_WNDPROC) : GetWindowLongPtrA(h, GWLP_WNDPROC));
    g_oldProc = prev;                                          // set before the hook can possibly run
    LONG_PTR r = g_uni ? SetWindowLongPtrW(h, GWLP_WNDPROC, (LONG_PTR)HookProc)
                       : SetWindowLongPtrA(h, GWLP_WNDPROC, (LONG_PTR)HookProc);
    if (!r) return -1;
    if ((WNDPROC)r != prev) g_oldProc = (WNDPROC)r;
    g_hwnd = h; g_mainTid = mainTid; g_pumpOn = true;
    PostMessageA(h, WM_VS_INIT, 0, 0);                         // wakes the window thread, which creates the timer
    return 1;
}

static void WriteMem(uint32_t a, const void* src, size_t n) {
    std::vector<uint8_t> copy((const uint8_t*)src, (const uint8_t*)src + n);
    bool ok = false;
    RunOnMain([&] { ok = Poke(a, &copy[0], n); });
    if (!ok) { char b[48]; snprintf(b, sizeof b, "0x%X", a); throw std::runtime_error(std::string("cannot write to address ") + b); }
}

static uint32_t U32(double d) { return (uint32_t)(int64_t)d; }
template <class T> static double Rd(double addr) {
    T v = 0; Peek(U32(addr), &v, sizeof v); return (double)v;
}

// ------------------------------------------------------------------- lexer
enum TT { T_NUM, T_ID, T_STR, T_OP };
struct Tok { TT t; std::string s; double n; };

static std::vector<Tok> Lex(const std::string& s) {
    std::vector<Tok> v; size_t i = 0, n = s.size();
    while (i < n) {
        unsigned char c = (unsigned char)s[i];
        if (isspace(c)) { ++i; continue; }
        if (c == '#' || (c == '/' && i + 1 < n && s[i + 1] == '/')) break;
        if (c == '"') {
            size_t j = i + 1; std::string r;
            while (j < n && s[j] != '"') r += s[j++];
            if (j >= n) throw std::runtime_error("string is missing closing quote");
            v.push_back(Tok{T_STR, r, 0}); i = j + 1; continue;
        }
        if (isdigit(c) || (c == '.' && i + 1 < n && isdigit((unsigned char)s[i + 1]))) {
            size_t j = i; double val;
            if (c == '0' && i + 1 < n && (s[i + 1] == 'x' || s[i + 1] == 'X')) {
                j = i + 2;
                while (j < n && isxdigit((unsigned char)s[j])) ++j;
                val = (double)strtoul(s.substr(i + 2, j - i - 2).c_str(), 0, 16);
            } else {
                while (j < n && (isdigit((unsigned char)s[j]) || s[j] == '.')) ++j;
                val = atof(s.substr(i, j - i).c_str());
            }
            v.push_back(Tok{T_NUM, s.substr(i, j - i), val}); i = j; continue;
        }
        if (isalpha(c) || c == '_') {
            size_t j = i;
            while (j < n && (isalnum((unsigned char)s[j]) || s[j] == '_')) ++j;
            v.push_back(Tok{T_ID, Lower(s.substr(i, j - i)), 0}); i = j; continue;
        }
        std::string op;
        if (i + 1 < n) {                          // two-character operators first (&& and || need this)
            static const char* two[] = {"==", "!=", "<=", ">=", "&&", "||", "+=", "-=", "*=", "/="};
            std::string d = s.substr(i, 2);
            for (size_t k = 0; k < 10; ++k) if (d == two[k]) { op = d; break; }
        }
        if (op.empty()) {
            if (!strchr("+-*/%(),=<>!{}", c))
                throw std::runtime_error(std::string("unexpected character '") + (char)c + "'");
            op = std::string(1, (char)c);
        }
        v.push_back(Tok{T_OP, op, 0}); i += op.size();
    }
    return v;
}

// --------------------------------------------------------------------- AST
struct Line { std::vector<Tok> t; int no; std::string file; };
struct Stmt {
    std::vector<Tok> t; std::vector<Stmt> body, other;
    int line = 0; std::string file; bool block = false;
};

struct Trigger {
    enum Kind { START, KEY, EVERY, WHEN };
    Kind k = START; int vk = 0; bool ctrl = false, shift = false, alt = false;
    int ms = 0; std::vector<Tok> cond; std::vector<Stmt> body; std::string where;
    std::atomic<bool> running{false}; bool prev = false; DWORD last = 0;
};

struct Func { std::vector<std::string> params; std::vector<Stmt> body; };
struct StopRun {};     // unwinds a whole trigger run (stop/exit inside a func called from an expression)
static thread_local int t_depth = 0;

struct Program {
    std::vector<std::unique_ptr<Trigger> > trig;
    std::map<std::string, Func> funcs;
    std::vector<Stmt> init;
    std::map<std::string, double> vars;
    std::mutex varMx;      // guards vars only; never held while calling game code or natives
    std::atomic<bool> alive{true};
    std::set<std::string> logged;
    DWORD t0 = 0;
};

static bool IsOp(const Tok& k, const char* s) { return k.t == T_OP && k.s == s; }

static std::vector<Stmt> ParseBlock(std::vector<Line>& L, size_t& i);

static Stmt ParseStmt(std::vector<Line>& L, size_t& i) {
    Stmt st; st.line = L[i].no; st.file = L[i].file; st.t = L[i].t;
    if (IsOp(st.t.back(), "{")) {
        st.block = true; st.t.pop_back(); ++i;
        st.body = ParseBlock(L, i);
        if (i >= L.size()) throw std::runtime_error(st.file + ":" + S(st.line) + ": missing }");
        Line& cl = L[i];
        if (cl.t.size() == 1) { ++i; }
        else if (cl.t.size() >= 3 && cl.t[1].s == "else" && IsOp(cl.t.back(), "{")
                 && !st.t.empty() && st.t[0].s == "if") {
            if (cl.t.size() == 3) {
                ++i; st.other = ParseBlock(L, i);
                if (i >= L.size() || L[i].t.size() != 1)
                    throw std::runtime_error(st.file + ":" + S(st.line) + ": missing } after else");
                ++i;
            } else {                                   // else if ... {
                std::vector<Tok> rest(cl.t.begin() + 2, cl.t.end());
                cl.t = rest;
                st.other.push_back(ParseStmt(L, i));
            }
        } else throw std::runtime_error(cl.file + ":" + S(cl.no) + ": unexpected text after }");
    } else ++i;
    return st;
}

static std::vector<Stmt> ParseBlock(std::vector<Line>& L, size_t& i) {
    std::vector<Stmt> out;
    while (i < L.size()) {
        if (L[i].t.empty()) { ++i; continue; }
        if (IsOp(L[i].t[0], "}")) break;
        out.push_back(ParseStmt(L, i));
    }
    return out;
}

static void ReadLines(const std::string& path, std::vector<Line>& out, int depth) {
    if (depth > 8) throw std::runtime_error("include nesting too deep");
    std::ifstream f(path.c_str());
    if (!f) throw std::runtime_error("cannot open " + path);
    std::string s; int n = 0;
    while (std::getline(f, s)) {
        ++n; std::vector<Tok> t;
        if (n == 1 && s.size() >= 3 && (unsigned char)s[0] == 0xEF && (unsigned char)s[1] == 0xBB && (unsigned char)s[2] == 0xBF)
            s.erase(0, 3);                                   // skip a UTF-8 byte-order mark
        try { t = Lex(s); }
        catch (std::exception& e) { throw std::runtime_error(path + ":" + S(n) + ": " + e.what()); }
        if (t.size() == 2 && t[0].s == "include" && t[1].t == T_STR) {
            ReadLines(g_dir + "VScript\\" + t[1].s, out, depth + 1); continue;
        }
        Line l; l.t = t; l.no = n; l.file = path; out.push_back(l);
    }
}

// ------------------------------------------------------------------- keys
static int KeyCode(const std::string& n) {
    if (n.empty()) return 0;
    if (n.size() == 1 && isalnum((unsigned char)n[0])) return toupper((unsigned char)n[0]);
    if (n[0] == 'f' && n.size() > 1 && isdigit((unsigned char)n[1])) {
        int k = atoi(n.c_str() + 1); if (k >= 1 && k <= 24) return VK_F1 + k - 1;
    }
    if (n.size() == 4 && n.compare(0, 3, "num") == 0 && isdigit((unsigned char)n[3]))
        return VK_NUMPAD0 + (n[3] - '0');
    static const struct { const char* n; int v; } T[] = {
        {"space", VK_SPACE}, {"enter", VK_RETURN}, {"tab", VK_TAB}, {"esc", VK_ESCAPE},
        {"up", VK_UP}, {"down", VK_DOWN}, {"left", VK_LEFT}, {"right", VK_RIGHT},
        {"backspace", VK_BACK}, {"delete", VK_DELETE}, {"insert", VK_INSERT},
        {"home", VK_HOME}, {"end", VK_END}, {"pageup", VK_PRIOR}, {"pagedown", VK_NEXT},
        {"ctrl", VK_CONTROL}, {"shift", VK_SHIFT}, {"alt", VK_MENU},
        {"plus", VK_OEM_PLUS}, {"minus", VK_OEM_MINUS}};
    for (size_t i = 0; i < sizeof T / sizeof T[0]; ++i) if (n == T[i].n) return T[i].v;
    return 0;
}
static bool Down(int vk) { return (GetAsyncKeyState(vk) & 0x8000) != 0; }

static bool KeyHeld(const Trigger& t) {
    if (t.ctrl && !Down(VK_CONTROL)) return false;
    if (t.shift && !Down(VK_SHIFT)) return false;
    if (t.alt && !Down(VK_MENU)) return false;
    return Down(t.vk);
}
static bool GameFocused() {
    DWORD pid = 0; GetWindowThreadProcessId(GetForegroundWindow(), &pid);
    return pid == GetCurrentProcessId();
}

// ------------------------------------------------------------- expressions
static double CallFunc(Program& P, const std::string& f, const std::vector<double>& a);
static double CallUser(Program& P, const std::string& name, const Func& fn, const std::vector<double>& a);

struct Ev {
    Program& P; const std::vector<Tok>& t; size_t p;
    Ev(Program& P_, const std::vector<Tok>& t_, size_t p_) : P(P_), t(t_), p(p_) {}
    bool End() const { return p >= t.size(); }
    bool Is(const char* s) const { return p < t.size() && IsOp(t[p], s); }
    void Expect(const char* s) {
        if (!Is(s)) throw std::runtime_error(std::string("expected '") + s + "'");
        ++p;
    }
    void Done() const { if (!End()) throw std::runtime_error("unexpected '" + t[p].s + "'"); }

    double Or() { double a = And(); while (Is("||")) { ++p; double b = And(); a = (a != 0 || b != 0); } return a; }
    double And() { double a = Cmp(); while (Is("&&")) { ++p; double b = Cmp(); a = (a != 0 && b != 0); } return a; }
    double Cmp() {
        double a = Add();
        if (Is("==")) { ++p; return a == Add(); }
        if (Is("!=")) { ++p; return a != Add(); }
        if (Is("<=")) { ++p; return a <= Add(); }
        if (Is(">=")) { ++p; return a >= Add(); }
        if (Is("<"))  { ++p; return a <  Add(); }
        if (Is(">"))  { ++p; return a >  Add(); }
        return a;
    }
    double Add() {
        double a = Mul();
        for (;;) {
            if (Is("+")) { ++p; a += Mul(); }
            else if (Is("-")) { ++p; a -= Mul(); }
            else return a;
        }
    }
    double Mul() {
        double a = Un();
        for (;;) {
            if (Is("*")) { ++p; a *= Un(); }
            else if (Is("/")) { ++p; double b = Un(); if (b == 0) throw std::runtime_error("division by zero"); a /= b; }
            else if (Is("%")) { ++p; double b = Un(); if (b == 0) throw std::runtime_error("division by zero"); a = fmod(a, b); }
            else return a;
        }
    }
    double Un() {
        if (Is("-")) { ++p; return -Un(); }
        if (Is("!")) { ++p; return Un() == 0; }
        return Prim();
    }
    double Prim() {
        if (End()) throw std::runtime_error("expression ended too early");
        const Tok& k = t[p];
        if (k.t == T_NUM) { ++p; return k.n; }
        if (IsOp(k, "(")) { ++p; double v = Or(); Expect(")"); return v; }
        if (k.t == T_ID) {
            ++p;
            if (Is("(")) {
                ++p; std::vector<double> a;
                if (!Is(")")) for (;;) { a.push_back(Or()); if (Is(",")) { ++p; continue; } break; }
                Expect(")");
                return CallFunc(P, k.s, a);
            }
            if (k.s == "true") return 1;
            if (k.s == "false") return 0;
            if (k.s == "pi") return 3.14159265358979;
            { std::lock_guard<std::mutex> g(P.varMx);
              std::map<std::string, double>::iterator it = P.vars.find(k.s);
              if (it != P.vars.end()) return it->second; }
            if (k.s.compare(0, 4, "key_") == 0) {
                int vk = KeyCode(k.s.substr(4));
                if (vk) return vk;
            }
            throw std::runtime_error("unknown variable '" + k.s + "'");
        }
        throw std::runtime_error("unexpected '" + k.s + "'");
    }
};

// Calls into the game. Floats must be passed as raw bits (see fbits()).
static int CallCdecl(uint32_t fn, const int32_t* r, size_t n) {
    uintptr_t f = (uintptr_t)fn;
    typedef int (__cdecl *C0)(); typedef int (__cdecl *C1)(int);
    typedef int (__cdecl *C2)(int, int); typedef int (__cdecl *C3)(int, int, int);
    typedef int (__cdecl *C4)(int, int, int, int); typedef int (__cdecl *C5)(int, int, int, int, int);
    typedef int (__cdecl *C6)(int, int, int, int, int, int);
    switch (n) {
    case 0: return reinterpret_cast<C0>(f)();
    case 1: return reinterpret_cast<C1>(f)(r[0]);
    case 2: return reinterpret_cast<C2>(f)(r[0], r[1]);
    case 3: return reinterpret_cast<C3>(f)(r[0], r[1], r[2]);
    case 4: return reinterpret_cast<C4>(f)(r[0], r[1], r[2], r[3]);
    case 5: return reinterpret_cast<C5>(f)(r[0], r[1], r[2], r[3], r[4]);
    default: return reinterpret_cast<C6>(f)(r[0], r[1], r[2], r[3], r[4], r[5]);
    }
}
// __thiscall = ECX holds 'this', rest on stack. __fastcall with a dummy EDX has the same layout.
static int CallThis(uint32_t fn, const int32_t* r, size_t n) {   // r[0] = this
    uintptr_t f = (uintptr_t)fn;
    typedef int (__fastcall *H1)(int, int); typedef int (__fastcall *H2)(int, int, int);
    typedef int (__fastcall *H3)(int, int, int, int); typedef int (__fastcall *H4)(int, int, int, int, int);
    typedef int (__fastcall *H5)(int, int, int, int, int, int);
    typedef int (__fastcall *H6)(int, int, int, int, int, int, int);
    switch (n) {
    case 1: return reinterpret_cast<H1>(f)(r[0], 0);
    case 2: return reinterpret_cast<H2>(f)(r[0], 0, r[1]);
    case 3: return reinterpret_cast<H3>(f)(r[0], 0, r[1], r[2]);
    case 4: return reinterpret_cast<H4>(f)(r[0], 0, r[1], r[2], r[3]);
    case 5: return reinterpret_cast<H5>(f)(r[0], 0, r[1], r[2], r[3], r[4]);
    default: return reinterpret_cast<H6>(f)(r[0], 0, r[1], r[2], r[3], r[4], r[5]);
    }
}

static double CallFunc(Program& P, const std::string& f, const std::vector<double>& a) {
    struct Arg {
        const std::string& f; const std::vector<double>& a;
        double operator()(size_t i) const {
            if (i >= a.size()) throw std::runtime_error(f + "(): missing argument");
            return a[i];
        }
    } A = {f, a};

    { std::map<std::string, Func>::iterator uf = P.funcs.find(f);   // funcs are immutable after compile
      if (uf != P.funcs.end()) return CallUser(P, f, uf->second, a); }

    if (f == "int")    return Rd<int32_t>(A(0));
    if (f == "uint")   return Rd<uint32_t>(A(0));
    if (f == "short")  return Rd<int16_t>(A(0));
    if (f == "ushort") return Rd<uint16_t>(A(0));
    if (f == "byte")   return Rd<uint8_t>(A(0));
    if (f == "float")  return Rd<float>(A(0));
    if (f == "ptr") {
        uint32_t addr = U32(A(0));
        for (size_t i = 1; i < a.size(); ++i) {
            int32_t v = 0;
            if (!Peek(addr, &v, 4) || v == 0) return 0;
            addr = (uint32_t)v + U32(a[i]);
        }
        return addr;
    }
    if (f == "call" || f == "thiscall") {
        bool th = (f == "thiscall");
        size_t n = a.size() - 1;
        if (a.empty() || n > 6 || (th && n < 1)) throw std::runtime_error(f + "(): bad argument count");
        int32_t r[8] = {0};
        for (size_t i = 0; i < n; ++i) r[i] = (int32_t)(int64_t)a[i + 1];
        uint32_t fn = U32(a[0]);
        int ret = 0;
        RunOnMain([&] { ret = th ? CallThis(fn, r, n) : CallCdecl(fn, r, n); });
        return ret;
    }
    if (f == "fbits") { float x = (float)A(0); int32_t b; memcpy(&b, &x, 4); return b; }
    if (f == "bitsf") { int32_t b = (int32_t)(int64_t)A(0); float x; memcpy(&x, &b, 4); return x; }
    if (f == "rand") {
        int lo = (int)A(0), hi = (int)A(1); if (hi < lo) std::swap(lo, hi);
        return lo + rand() % (hi - lo + 1);
    }
    // VC 1.0 addresses (from skygfx_vc / Plugin-SDK)
    if (f == "hour")   return Rd<uint8_t>(0xA10B6B);
    if (f == "minute") return Rd<uint8_t>(0xA10B92);
    if (f == "setweather") {                       // writes Old + New weather (both are shorts)
        int16_t v = (int16_t)(int64_t)A(0);
        WriteMem(0xA10A2E, &v, 2); WriteMem(0xA10AAA, &v, 2);
        return 0;
    }
    if (f == "time")  return (double)(GetTickCount() - P.t0);
    if (f == "down")  return Down((int)A(0)) ? 1 : 0;
    if (f == "abs")   return fabs(A(0));
    if (f == "min")   return std::min(A(0), A(1));
    if (f == "max")   return std::max(A(0), A(1));
    if (f == "floor") return floor(A(0));
    if (f == "ceil")  return ceil(A(0));
    if (f == "sqrt")  return sqrt(A(0));
    if (f == "sin")   return sin(A(0));
    if (f == "cos")   return cos(A(0));

    VSNative fn = 0;
    { std::lock_guard<std::mutex> l(g_nativeMx);
      std::map<std::string, VSNative>::iterator it = g_natives.find(f);
      if (it != g_natives.end()) fn = it->second; }
    if (fn) {                                     // no VScript lock is held here, so natives may call back
        double r = 0;
        RunOnMain([&] { r = fn((int)a.size(), a.empty() ? 0 : &a[0]); });
        return r;
    }
    throw std::runtime_error("unknown function '" + f + "'");
}
static bool IsNative(const std::string& n) {
    std::lock_guard<std::mutex> l(g_nativeMx);
    return g_natives.count(n) != 0;
}

// ------------------------------------------------------------------ runner
static std::string Fmt(double v) {
    char b[64];
    if (v == floor(v) && fabs(v) < 1e15) snprintf(b, sizeof b, "%.0f", v);
    else snprintf(b, sizeof b, "%g", v);
    return b;
}
static void LogOnce(Program& P, const std::string& m) {
    { std::lock_guard<std::mutex> l(g_logMx); if (!P.logged.insert(m).second) return; }
    Log(m);
}

enum Flow { F_NEXT = 0, F_RETURN, F_STOP, F_BREAK };

struct Runner {
    Program* P = 0; double ret = 0;     // ret = value of the last "return expr"

    double Eval(const std::vector<Tok>& t, size_t from) {
        Ev e(*P, t, from); double v = e.Or(); e.Done(); return v;
    }
    std::vector<double> Args(const std::vector<Tok>& t, size_t from) {
        Ev e(*P, t, from); std::vector<double> r;
        while (!e.End()) { r.push_back(e.Or()); if (e.Is(",")) ++e.p; else break; }
        e.Done(); return r;
    }
    std::string Text(const std::vector<Tok>& t, size_t from) {
        Ev e(*P, t, from); std::string out;
        while (!e.End()) {
            if (t[e.p].t == T_STR && (e.p + 1 >= t.size() || IsOp(t[e.p + 1], ","))) { out += t[e.p].s; ++e.p; }
            else out += Fmt(e.Or());
            if (e.Is(",")) ++e.p; else break;
        }
        e.Done(); return out;
    }
    void Wait(double ms) {
        DWORD end = GetTickCount() + (DWORD)(ms < 0 ? 0 : ms);
        Sleep(1);
        while (P->alive) {
            int left = (int)(end - GetTickCount());
            if (left <= 0) break;
            Sleep(std::min(left, 20));
        }
    }
    Flow Block(const std::vector<Stmt>& b) {
        for (size_t i = 0; i < b.size(); ++i) {
            if (!P->alive) return F_STOP;
            Flow f = One(b[i]); if (f != F_NEXT) return f;
        }
        return F_NEXT;
    }
    Flow One(const Stmt& s) {
        try { return Do(s); }
        catch (std::exception& e) {
            std::string m = e.what();
            if (m.compare(0, s.file.size(), s.file) == 0 && m.find(": ") != std::string::npos) throw;
            throw std::runtime_error(s.file + ":" + S(s.line) + ": " + m);
        }
    }
    static void NeedBlock(const Stmt& s, const std::string& k) {
        if (!s.block) throw std::runtime_error("missing { after " + k);
    }
    void Write(const std::string& ty, double addr, double val) {
        uint8_t buf[4]; size_t n;
        if (ty == "byte")       { buf[0] = (uint8_t)(int64_t)val; n = 1; }
        else if (ty == "short") { int16_t v = (int16_t)(int64_t)val; memcpy(buf, &v, 2); n = 2; }
        else if (ty == "int")   { int32_t v = (int32_t)(int64_t)val; memcpy(buf, &v, 4); n = 4; }
        else if (ty == "float") { float v = (float)val; memcpy(buf, &v, 4); n = 4; }
        else throw std::runtime_error("poke type must be byte, short, int or float");
        WriteMem(U32(addr), buf, n);
    }

    Flow Do(const Stmt& s) {
        const std::vector<Tok>& t = s.t;
        std::string k = (t[0].t == T_ID) ? t[0].s : "";

        // assignment:  x = ..   x += ..
        if (t.size() >= 3 && t[0].t == T_ID && t[1].t == T_OP &&
            (t[1].s == "=" || t[1].s == "+=" || t[1].s == "-=" || t[1].s == "*=" || t[1].s == "/=")) {
            Ev e(*P, t, 2); double v = e.Or(); e.Done();   // evaluated without holding any lock
            const std::string& op = t[1].s;
            std::lock_guard<std::mutex> g(P->varMx);        // only the read-modify-write is locked
            if (op == "=") { P->vars[k] = v; return F_NEXT; }
            std::map<std::string, double>::iterator it = P->vars.find(k);
            if (it == P->vars.end()) throw std::runtime_error("unknown variable '" + k + "'");
            if (op == "+=") it->second += v;
            else if (op == "-=") it->second -= v;
            else if (op == "*=") it->second *= v;
            else { if (v == 0) throw std::runtime_error("division by zero"); it->second /= v; }
            return F_NEXT;
        }
        if (k == "if") {
            NeedBlock(s, k);
            return Eval(t, 1) != 0 ? Block(s.body) : Block(s.other);
        }
        if (k == "while") {
            NeedBlock(s, k);
            while (P->alive && Eval(t, 1) != 0) {
                Flow f = Block(s.body);
                if (f == F_BREAK) break;
                if (f != F_NEXT) return f;
                Sleep(1);
            }
            return F_NEXT;
        }
        if (k == "repeat") {
            NeedBlock(s, k);
            int n = (int)Eval(t, 1);
            for (int i = 0; i < n && P->alive; ++i) {
                Flow f = Block(s.body);
                if (f == F_BREAK) break;
                if (f != F_NEXT) return f;
            }
            return F_NEXT;
        }
        if (k == "break")  return F_BREAK;
        if (k == "return") { ret = (t.size() > 1) ? Eval(t, 1) : 0; return F_RETURN; }
        if (k == "stop")   return F_STOP;                       // ends this trigger run
        if (k == "exit")   { P->alive = false; return F_STOP; } // ends the whole script
        if (k == "wait") {
            std::vector<double> a = Args(t, 1);
            if (a.size() != 1) throw std::runtime_error("wait needs one number (milliseconds)");
            Wait(a[0]); return F_NEXT;
        }
        if (k == "run") {
            if (t.size() != 2 || t[1].t != T_ID) throw std::runtime_error("use: run name   (or call it as name(args))");
            std::map<std::string, Func>::iterator it = P->funcs.find(t[1].s);
            if (it == P->funcs.end()) throw std::runtime_error("unknown func '" + t[1].s + "'");
            CallUser(*P, it->first, it->second, std::vector<double>());   // return value is discarded
            return F_NEXT;
        }
        if (k == "print" || k == "log") { Log("[script] " + Text(t, 1)); return F_NEXT; }
        if (k == "alert") { MessageBoxA(NULL, Text(t, 1).c_str(), "VScript", MB_OK | MB_TOPMOST); return F_NEXT; }
        if (k == "poke") {
            if (t.size() < 3 || t[1].t != T_ID) throw std::runtime_error("use: poke int|short|byte|float ADDR, value");
            std::vector<double> a = Args(t, 2);
            if (a.size() != 2) throw std::runtime_error("use: poke type ADDR, value");
            Write(t[1].s, a[0], a[1]); return F_NEXT;
        }
        if (k == "nop") {
            std::vector<double> a = Args(t, 1);
            if (a.size() != 2 || a[1] < 1 || a[1] > 4096) throw std::runtime_error("use: nop ADDR, count");
            std::vector<uint8_t> v((size_t)a[1], 0x90);
            WriteMem(U32(a[0]), &v[0], v.size());
            return F_NEXT;
        }
        if (k == "patch") {
            std::vector<double> a = Args(t, 1);
            if (a.size() < 2) throw std::runtime_error("use: patch ADDR, byte, byte, ...");
            std::vector<uint8_t> v;
            for (size_t i = 1; i < a.size(); ++i) v.push_back((uint8_t)(int64_t)a[i]);
            WriteMem(U32(a[0]), &v[0], v.size());
            return F_NEXT;
        }
        // function call as a statement, or a command registered by another plugin
        if (t[0].t == T_ID && ((t.size() > 1 && IsOp(t[1], "(")) )) { Eval(t, 0); return F_NEXT; }
        if (k == "setweather") {
            std::vector<double> a = Args(t, 1);
            CallFunc(*P, k, a); return F_NEXT;
        }
        if (t[0].t == T_ID && IsNative(k)) {
            std::vector<double> a = Args(t, 1);
            CallFunc(*P, k, a); return F_NEXT;
        }
        throw std::runtime_error("unknown command '" + t[0].s + "'");
    }
};

static double CallUser(Program& P, const std::string& name, const Func& fn, const std::vector<double>& a) {
    if (a.size() != fn.params.size())
        throw std::runtime_error("func '" + name + "' takes " + S((long)fn.params.size()) + " argument(s)");
    if (t_depth >= 32) throw std::runtime_error("func calls nested too deep");
    { std::lock_guard<std::mutex> g(P.varMx);               // parameters are plain global variables
      for (size_t i = 0; i < a.size(); ++i) P.vars[fn.params[i]] = a[i]; }
    struct Depth { Depth() { ++t_depth; } ~Depth() { --t_depth; } } depth;
    Runner r; r.P = &P;
    Flow f = r.Block(fn.body);
    if (f == F_STOP) throw StopRun();
    return f == F_RETURN ? r.ret : 0;                       // no "return" -> 0
}

// ------------------------------------------------------------- compilation
static std::shared_ptr<Program> Compile(const std::string& path) {
    std::shared_ptr<Program> P = std::make_shared<Program>();
    P->t0 = GetTickCount();
    // VC 1.0 constants (scripts may overwrite them). Sources: skygfx_vc, Plugin-SDK plugin_vc.
    P->vars["new_weather"] = 0xA10A2E;      // short
    P->vars["old_weather"] = 0xA10AAA;      // short
    P->vars["weather_interp"] = 0x9787D8;   // float
    P->vars["clock_hours"] = 0xA10B6B;      // byte
    P->vars["clock_minutes"] = 0xA10B92;    // byte
    P->vars["players"] = 0x94AD28;          // CPlayerInfo array
    P->vars["player_in_focus"] = 0xA10AFB;  // byte
    std::vector<Line> L; ReadLines(path, L, 0);
    size_t i = 0;
    while (i < L.size()) {
        if (L[i].t.empty()) { ++i; continue; }
        if (IsOp(L[i].t[0], "}")) throw std::runtime_error(L[i].file + ":" + S(L[i].no) + ": unexpected }");
        Stmt s = ParseStmt(L, i);
        std::string k = (s.t[0].t == T_ID) ? s.t[0].s : "";
        std::string where = s.file + ":" + S(s.line) + ": ";

        if (k == "on" || k == "key" || k == "every" || k == "when") {
            if (!s.block) throw std::runtime_error(where + "missing { after " + k);
            std::unique_ptr<Trigger> tr(new Trigger);
            tr->body = s.body; tr->where = where;
            if (k == "on") {
                if (s.t.size() == 2 && (s.t[1].s == "start" || s.t[1].s == "game_start")) tr->k = Trigger::START;
                else throw std::runtime_error(where + "use: on start");
            } else if (k == "key") {
                tr->k = Trigger::KEY;
                for (size_t j = 1; j < s.t.size(); ++j) {
                    if (IsOp(s.t[j], "+")) continue;
                    std::string n = Lower(s.t[j].s); int vk = KeyCode(n);
                    if (!vk) throw std::runtime_error(where + "unknown key '" + n + "'");
                    if (vk == VK_CONTROL) tr->ctrl = true;
                    else if (vk == VK_SHIFT) tr->shift = true;
                    else if (vk == VK_MENU) tr->alt = true;
                    else if (tr->vk) throw std::runtime_error(where + "only one normal key allowed");
                    else tr->vk = vk;
                }
                if (!tr->vk) throw std::runtime_error(where + "key needs a normal key, e.g. key ctrl+F5");
            } else if (k == "every") {
                if (s.t.size() != 2 || s.t[1].t != T_NUM) throw std::runtime_error(where + "use: every 500 {");
                tr->k = Trigger::EVERY; tr->ms = std::max(1, (int)s.t[1].n); tr->last = GetTickCount();
            } else {
                if (s.t.size() < 2) throw std::runtime_error(where + "when needs a condition");
                tr->k = Trigger::WHEN; tr->cond.assign(s.t.begin() + 1, s.t.end());
            }
            P->trig.push_back(std::move(tr));
        } else if (k == "func") {
            const std::vector<Tok>& h = s.t;
            if (!s.block || h.size() < 2 || h[1].t != T_ID) throw std::runtime_error(where + "use: func name(a, b) {");
            Func fn; fn.body = s.body; size_t j = 2;
            if (j < h.size()) {
                if (!IsOp(h[j], "(")) throw std::runtime_error(where + "use: func name(a, b) {");
                ++j;
                while (j < h.size() && !IsOp(h[j], ")")) {
                    if (h[j].t != T_ID) throw std::runtime_error(where + "bad parameter list");
                    fn.params.push_back(h[j].s); ++j;
                    if (j < h.size() && IsOp(h[j], ",")) ++j;
                }
                if (j >= h.size() || j + 1 != h.size()) throw std::runtime_error(where + "bad parameter list");
            }
            P->funcs[h[1].s] = fn;
        } else {
            P->init.push_back(s);          // top-level lines (e.g. variables) run at load
        }
    }
    return P;
}

static void Fire(const std::shared_ptr<Program>& P, Trigger* t) {
    bool exp = false;
    if (!t->running.compare_exchange_strong(exp, true)) return;     // still running: skip
    ++g_threads;
    try {
        std::thread([P, t]() {
            Runner r; r.P = P.get();
            try { r.Block(t->body); }
            catch (std::exception& e) { LogOnce(*P, e.what()); }
            catch (StopRun&) {}
            catch (...) {}
            t->running = false;
            --g_threads;
        }).detach();
    } catch (...) { t->running = false; --g_threads; }
}

static void SchedulerLoop(const std::shared_ptr<Program>& P) {
    while (P->alive) {
        Sleep(5);
        bool focus = GameFocused(); DWORD now = GetTickCount();
        for (size_t i = 0; i < P->trig.size(); ++i) {
            Trigger& t = *P->trig[i]; bool fire = false;
            if (t.k == Trigger::EVERY) {
                if (now - t.last >= (DWORD)t.ms) { t.last = now; fire = true; }
            } else if (t.k == Trigger::KEY) {
                bool d = focus && KeyHeld(t);
                if (d && !t.prev) fire = true;
                t.prev = d;
            } else if (t.k == Trigger::WHEN) {
                bool v = false;
                try {
                    Ev e(*P, t.cond, 0); v = e.Or() != 0; e.Done();
                } catch (std::exception& ex) { LogOnce(*P, t.where + ex.what()); } catch (StopRun&) {}
                if (v && !t.prev) fire = true;
                t.prev = v;
            }
            if (fire) Fire(P, &t);
        }
    }
}

static void StartProgram(std::shared_ptr<Program> P) {
    { Runner r; r.P = P.get();
      try { r.Block(P->init); } catch (std::exception& e) { LogOnce(*P, e.what()); } catch (StopRun&) {} }
    for (size_t i = 0; i < P->trig.size(); ++i)
        if (P->trig[i]->k == Trigger::START) Fire(P, P->trig[i].get());
    ++g_threads;
    try { std::thread([P]() { SchedulerLoop(P); --g_threads; }).detach(); } catch (...) { --g_threads; }
}

// -------------------------------------------------------------- entry point
static bool Stamp(const std::string& path, FILETIME& ft) {
    WIN32_FILE_ATTRIBUTE_DATA d;
    if (!GetFileAttributesExA(path.c_str(), GetFileExInfoStandard, &d)) return false;
    ft = d.ftLastWriteTime; return true;
}

static DWORD WINAPI MainThread(LPVOID) {
    char exe[MAX_PATH]; GetModuleFileNameA(NULL, exe, MAX_PATH);
    std::string d = exe; g_dir = d.substr(0, d.find_last_of("\\/") + 1);
    CreateDirectoryA((g_dir + "VScript").c_str(), NULL);
    Log("VScript attached. Game folder: " + g_dir);
    std::string ini = g_dir + "VScript\\VScript.ini";
    int delay = GetPrivateProfileIntA("VScript", "StartDelay", 4000, ini.c_str());
    bool hot = GetPrivateProfileIntA("VScript", "HotReload", 1, ini.c_str()) != 0;
    srand(GetTickCount());
    for (int t = 0; t < delay && !g_quit; t += 50) Sleep(50);
    int hk = 0;                                                        // wait up to 30 s for the game window
    for (int i = 0; i < 120 && hk == 0 && !g_quit; ++i) { hk = InstallHook(); if (hk == 0) Sleep(250); }
    Log(g_pumpOn ? "game-thread pump installed"
                 : "WARNING: could not hook the game window; game writes/calls will run on script threads");

    std::string main = g_dir + "VScript\\main.vscript";
    std::shared_ptr<Program> cur; FILETIME last; memset(&last, 0, sizeof last); bool seen = false, warned = false;
    while (!g_quit) {
        FILETIME ft;
        bool have = Stamp(main, ft);
        if (!have && !seen && !warned) { warned = true; Log("waiting for " + main + " (file not found)"); }
        if (have && (!seen || CompareFileTime(&ft, &last) != 0)) {
            seen = true; last = ft;
            try {
                std::shared_ptr<Program> np = Compile(main);
                if (cur) cur->alive = false;           // stop old scripts only once the new one compiled
                cur = np;
                { std::lock_guard<std::mutex> l(g_curMx); g_cur = np; }
                StartProgram(np);
                Log("script loaded: " + main);
            } catch (std::exception& e) { Log(std::string("load error: ") + e.what()); }
        }
        if (!hot && seen) break;
        Sleep(500);
    }
    --g_threads;
    return 0;
}

// Clean stop: ends all scripts, waits for the threads, removes the timer and restores the window procedure.
extern "C" __declspec(dllexport) void VScript_Shutdown() {
    g_quit = true;
    { std::lock_guard<std::mutex> l(g_curMx); if (g_cur) g_cur->alive = false; }
    bool onGame = g_pumpOn && GetCurrentThreadId() == g_mainTid;
    for (int i = 0; i < 300 && g_threads > 0; ++i) { if (onGame) Pump(); Sleep(10); }
    if (g_pumpOn && g_hwnd) {
        DWORD_PTR res = 0;                       // synchronous: HookProc handles it on the window's own thread
        if (!SendMessageTimeoutA(g_hwnd, WM_VS_EXIT, 0, 0, SMTO_ABORTIFHUNG, 1000, &res)) Log("shutdown: window did not answer");
    }
    Log("shutdown complete, threads still running: " + S((long)g_threads.load()));
    std::lock_guard<std::mutex> l(g_curMx); g_cur.reset();
}

extern "C" __declspec(dllexport) void VScript_Register(const char* name, VSNative fn) {
    if (!name || !fn) return;
    std::lock_guard<std::mutex> l(g_nativeMx);
    g_natives[Lower(name)] = fn;
}

extern "C" BOOL APIENTRY DllMain(HMODULE hModule, DWORD reason, LPVOID) {   // extern "C": MinGW will not find a mangled DllMain
    if (reason == DLL_PROCESS_ATTACH) {
        (void)hModule;           // (no DisableThreadLibraryCalls: unsafe with a statically linked CRT)
        HMODULE pin = NULL;      // detached threads run code from this DLL: never let it be unloaded under them
        GetModuleHandleExA(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS | GET_MODULE_HANDLE_EX_FLAG_PIN, (LPCSTR)&DllMain, &pin);
        ++g_threads;
        HANDLE h = CreateThread(NULL, 0, MainThread, NULL, 0, NULL);
        if (h) CloseHandle(h); else --g_threads;
    }
    return TRUE;
}
