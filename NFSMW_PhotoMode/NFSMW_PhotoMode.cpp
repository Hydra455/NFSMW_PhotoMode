

#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <math.h>
#include <d3d9.h>
#include <mmdeviceapi.h>
#include <audiopolicy.h>

#pragma comment(lib, "ole32.lib")

struct Vec3
{
    float x, y, z;
};

struct Mat4
{
    float m[16];
};

#define VK_0 0x30
#define VK_9 0x39

static bool gPhotoActive = false;
static bool gF8WasDown = false;
static bool gEscWasDown = false;
static bool gOrbitInitialized = false;
static DWORD gLastOrbitTick = 0;

static float gYaw = 0.0f;
static float gPitch = 0.20f;
static float gDistance = 5.5f;

static const unsigned long kTweakGameSpeed    = 0x00901B1Cu;
static const unsigned long kD3DDevicePtr      = 0x00982BDCu;

static const unsigned long kDrawHudInstruction = 0x0057CAA7u;
static const unsigned long kDrawHudImmediate   = 0x0057CAA8u;

struct AudioSessionMuteState
{
    ISimpleAudioVolume* volume;
    BOOL wasMuted;
};
static AudioSessionMuteState gAudioSessions[16];
static unsigned int gAudioSessionCount = 0;
static bool gAudioMuteApplied = false;
static bool gAudioComOwned = false;

static bool gPhotoStateApplied = false;
static float gSavedGameSpeed = 1.0f;
static unsigned char gSavedDrawHud = 1u;
static bool gHudPatched = false;

static bool gFreezePending = false;
static bool gWorldFrozen = false;
static DWORD gHudHideTick = 0;
static const DWORD kHudPropagationDelayMs = 100u;

typedef HRESULT (WINAPI *Present_t)(IDirect3DDevice9*, const RECT*, const RECT*, HWND, const RGNDATA*);
static Present_t gChainedPresent = 0;
static void** gPresentSlot = 0;
static bool gOverlayHookInstalled = false;
static volatile LONG gShutdown = 0;

static const unsigned long kLookAtCallSite = 0x0047DCBCu;
static const unsigned long kCreateLookAt   = 0x006CF0A0u;

typedef void (__cdecl *CreateLookAt_t)(Mat4*, const Vec3*, const Vec3*, const Vec3*);
static CreateLookAt_t gChainedLookAt = 0;

static const unsigned long kPausePopulateCallA       = 0x005463A6u;
static const unsigned long kPausePopulateCallB       = 0x005463ADu;
static const unsigned long kPauseMenuVtable          = 0x0089E5A0u;
static const unsigned long kPauseOptionRetailVtable  = 0x0089C25Cu;
static const unsigned long kJMalloc                  = 0x00652AD0u;
static const unsigned long kPauseOptionCtor          = 0x0051D790u;
static const unsigned long kIconScrollerAddOption    = 0x00573960u;
static const unsigned long kUnPause                  = 0x00632190u;
static const unsigned long kLocalizationLookup       = 0x0056BB80u;

static const unsigned long kPhotoModeIconHash  = 0xC3400A65u;
static const unsigned long kPhotoModeLabelHash = 0x92550DD0u;
static const unsigned long kAcceptEventHash    = 0x0C407210u;

typedef void (__thiscall *PausePopulate_t)(void*);
static PausePopulate_t gChainedPausePopulateA = 0;
static PausePopulate_t gChainedPausePopulateB = 0;
static unsigned char gPausePopulateOriginalA[5] = {0};
static unsigned char gPausePopulateOriginalB[5] = {0};
static bool gPausePopulateHookAInstalled = false;
static bool gPausePopulateHookBInstalled = false;
static void* gPauseMenuInjected = 0;

typedef const char* (__fastcall *LocalizationLookup_t)(void*, unsigned int);
static LocalizationLookup_t gLocalizationTrampoline = 0;
static unsigned char gLocalizationOriginal[7] = {0};
static bool gLocalizationHookInstalled = false;

static unsigned long gPhotoOptionVtable[12] = {0};
static bool gPhotoOptionVtableReady = false;

static volatile LONG gPausePhotoRequested = 0;
static DWORD gPausePhotoRequestTick = 0;
static const DWORD kPauseToPhotoDelayMs = 220u;

static bool BytesEqual(const unsigned char* p, const unsigned char* expected, unsigned int n)
{
    for (unsigned int i = 0; i < n; ++i)
        if (p[i] != expected[i]) return false;
    return true;
}

static bool IsKeyDown(int vk)
{
    SHORT state = GetAsyncKeyState(vk);
    return (state & static_cast<SHORT>(0x8000)) != 0;
}

static float ClampFloat(float v, float lo, float hi)
{
    if (v < lo) return lo;
    if (v > hi) return hi;
    return v;
}

static float VecLength(const Vec3& v)
{
    return sqrtf(v.x * v.x + v.y * v.y + v.z * v.z);
}

static bool ReasonableVec(const Vec3* v)
{
    if (!v) return false;
    const float limit = 1000000.0f;
    return v->x == v->x && v->y == v->y && v->z == v->z &&
           v->x > -limit && v->x < limit &&
           v->y > -limit && v->y < limit &&
           v->z > -limit && v->z < limit;
}

static bool WriteProtected(void* address, const void* data, unsigned int size)
{
    if (!address || !data || !size) return false;
    DWORD oldProtect = 0;
    if (!VirtualProtect(address, size, PAGE_EXECUTE_READWRITE, &oldProtect))
        return false;

    const unsigned char* src = reinterpret_cast<const unsigned char*>(data);
    unsigned char* dst = reinterpret_cast<unsigned char*>(address);
    for (unsigned int i = 0; i < size; ++i) dst[i] = src[i];

    DWORD ignored = 0;
    VirtualProtect(address, size, oldProtect, &ignored);
    FlushInstructionCache(GetCurrentProcess(), address, size);
    return true;
}

static bool IsReadableRange(const void* address, unsigned int size)
{
    if (!address || !size) return false;

    MEMORY_BASIC_INFORMATION mbi;
    if (!VirtualQuery(address, &mbi, sizeof(mbi))) return false;
    if (mbi.State != MEM_COMMIT) return false;
    if ((mbi.Protect & PAGE_GUARD) || (mbi.Protect & PAGE_NOACCESS)) return false;

    const unsigned long begin = reinterpret_cast<unsigned long>(address);
    const unsigned long regionBegin = reinterpret_cast<unsigned long>(mbi.BaseAddress);
    const unsigned long regionEnd = regionBegin + static_cast<unsigned long>(mbi.RegionSize);
    if (begin < regionBegin) return false;
    if (begin + size < begin) return false;
    return begin + size <= regionEnd;
}

static bool IsExecutableAddress(const void* address)
{
    if (!address) return false;
    MEMORY_BASIC_INFORMATION mbi;
    if (!VirtualQuery(address, &mbi, sizeof(mbi))) return false;
    if (mbi.State != MEM_COMMIT) return false;
    const DWORD p = mbi.Protect & 0xFFu;
    return p == PAGE_EXECUTE || p == PAGE_EXECUTE_READ ||
           p == PAGE_EXECUTE_READWRITE || p == PAGE_EXECUTE_WRITECOPY;
}

static unsigned long ResolveRelativeCallTargetA4(unsigned long address)
{
    const unsigned char* p = reinterpret_cast<const unsigned char*>(address);
    if (!IsReadableRange(p, 5u) || p[0] != 0xE8u) return 0u;
    const long rel = *reinterpret_cast<const long*>(p + 1);
    return address + 5u + static_cast<unsigned long>(rel);
}

static bool PatchRelativeCallDirect(unsigned long address, void* destination)
{
    unsigned char patch[5];
    patch[0] = 0xE8u;
    const long rel = static_cast<long>(
        reinterpret_cast<unsigned long>(destination) - (address + 5u));
    *reinterpret_cast<long*>(patch + 1) = rel;
    return WriteProtected(reinterpret_cast<void*>(address), patch, 5u);
}

static const char* __fastcall NFSMW_PhotoMode_LocalizationHook(void*, unsigned int hash)
{
    if (hash == kPhotoModeLabelHash)
        return "PHOTO MODE";

    LocalizationLookup_t original = gLocalizationTrampoline;
    return original ? original(0, hash) : 0;
}

static bool InstallLocalizationHook()
{
    const unsigned char expected[7] =
        {0x53u,0x8Bu,0x1Du,0x80u,0xCFu,0x91u,0x00u};
    const unsigned char* entry =
        reinterpret_cast<const unsigned char*>(kLocalizationLookup);

    if (!IsReadableRange(entry, 7u) || !BytesEqual(entry, expected, 7u))
    {
        return false;
    }

    for (unsigned int i = 0; i < 7u; ++i)
        gLocalizationOriginal[i] = entry[i];

    unsigned char* trampoline = reinterpret_cast<unsigned char*>(
        VirtualAlloc(0, 16u, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE));
    if (!trampoline)
    {
        return false;
    }

    for (unsigned int i = 0; i < 7u; ++i)
        trampoline[i] = gLocalizationOriginal[i];

    trampoline[7] = 0xE9u;
    *reinterpret_cast<long*>(trampoline + 8) = static_cast<long>(
        (kLocalizationLookup + 7u) -
        (reinterpret_cast<unsigned long>(trampoline) + 12u));

    gLocalizationTrampoline =
        reinterpret_cast<LocalizationLookup_t>(trampoline);

    unsigned char patch[7];
    patch[0] = 0xE9u;
    *reinterpret_cast<long*>(patch + 1) = static_cast<long>(
        reinterpret_cast<unsigned long>(&NFSMW_PhotoMode_LocalizationHook) -
        (kLocalizationLookup + 5u));
    patch[5] = 0x90u;
    patch[6] = 0x90u;

    if (!WriteProtected(reinterpret_cast<void*>(kLocalizationLookup), patch, 7u))
    {
        VirtualFree(trampoline, 0, MEM_RELEASE);
        gLocalizationTrampoline = 0;
        return false;
    }

    gLocalizationHookInstalled = true;
    return true;
}

static void RestoreLocalizationHook()
{
    if (!gLocalizationHookInstalled) return;

    const unsigned char* p =
        reinterpret_cast<const unsigned char*>(kLocalizationLookup);
    if (IsReadableRange(p, 5u) && p[0] == 0xE9u)
    {
        const long rel = *reinterpret_cast<const long*>(p + 1);
        const unsigned long target =
            kLocalizationLookup + 5u + static_cast<unsigned long>(rel);
        if (target ==
            reinterpret_cast<unsigned long>(&NFSMW_PhotoMode_LocalizationHook))
        {
            WriteProtected(reinterpret_cast<void*>(kLocalizationLookup),
                           gLocalizationOriginal, 7u);
        }
    }

    if (gLocalizationTrampoline)
    {
        VirtualFree(reinterpret_cast<void*>(gLocalizationTrampoline),
                    0, MEM_RELEASE);
        gLocalizationTrampoline = 0;
    }
    gLocalizationHookInstalled = false;
}

typedef void* (__cdecl *JMalloc_t)(unsigned int);
typedef void* (__thiscall *PauseOptionCtor_t)(
    void*, unsigned long, unsigned long, unsigned long);
typedef void (__thiscall *IconScrollerAddOption_t)(void*, void*);
typedef void (__cdecl *UnPause_t)();

static void __fastcall NFSMW_PhotoMode_OptionReact(
    void*, void*, const char*, unsigned int data, void*,
    unsigned int, unsigned int)
{
    if (data != kAcceptEventHash)
        return;

    if (gPhotoActive ||
        InterlockedCompareExchange(&gPausePhotoRequested, 0, 0) != 0)
        return;

    gPausePhotoRequestTick = GetTickCount();
    InterlockedExchange(&gPausePhotoRequested, 1);
    UnPause_t unpause = reinterpret_cast<UnPause_t>(kUnPause);
    unpause();
}

static bool PreparePhotoOptionVtable()
{
    if (gPhotoOptionVtableReady) return true;

    const unsigned long* retail =
        reinterpret_cast<const unsigned long*>(kPauseOptionRetailVtable);
    if (!IsReadableRange(retail, sizeof(gPhotoOptionVtable)))
        return false;

    for (unsigned int i = 0; i < 12u; ++i)
        gPhotoOptionVtable[i] = retail[i];

    gPhotoOptionVtable[1] =
        reinterpret_cast<unsigned long>(&NFSMW_PhotoMode_OptionReact);
    gPhotoOptionVtableReady = true;
    return true;
}

static bool AddPhotoModePauseOption(void* pauseMenu)
{
    if (!pauseMenu || !IsReadableRange(pauseMenu, 0x14Cu))
        return false;

    if (*reinterpret_cast<unsigned long*>(pauseMenu) != kPauseMenuVtable)
    {
        return false;
    }

    if (gPauseMenuInjected == pauseMenu)
    {
        return true;
    }

    if (!PreparePhotoOptionVtable())
    {
        return false;
    }

    JMalloc_t jMalloc = reinterpret_cast<JMalloc_t>(kJMalloc);
    PauseOptionCtor_t createOption =
        reinterpret_cast<PauseOptionCtor_t>(kPauseOptionCtor);
    IconScrollerAddOption_t addOption =
        reinterpret_cast<IconScrollerAddOption_t>(kIconScrollerAddOption);

    void* option = jMalloc(0x4Cu);
    if (!option)
    {
        return false;
    }

    createOption(option, kPhotoModeIconHash, kPhotoModeLabelHash, 0u);
    *reinterpret_cast<unsigned long*>(option) =
        reinterpret_cast<unsigned long>(gPhotoOptionVtable);

    addOption(pauseMenu, option);
    gPauseMenuInjected = pauseMenu;
    return true;
}

static void __fastcall NFSMW_PhotoMode_PausePopulateHookA(void* pauseMenu, void*)
{
    PausePopulate_t original = gChainedPausePopulateA;
    if (original) original(pauseMenu);
    AddPhotoModePauseOption(pauseMenu);
}

static void __fastcall NFSMW_PhotoMode_PausePopulateHookB(void* pauseMenu, void*)
{
    PausePopulate_t original = gChainedPausePopulateB;
    if (original) original(pauseMenu);
    AddPhotoModePauseOption(pauseMenu);
}

static bool InstallOnePausePopulationHook(
    unsigned long callSite,
    void* hook,
    PausePopulate_t* chained,
    unsigned char originalBytes[5],
    bool* installed)
{
    unsigned char* p = reinterpret_cast<unsigned char*>(callSite);
    if (!IsReadableRange(p, 5u) || p[0] != 0xE8u)
    {
        return false;
    }

    for (unsigned int i = 0; i < 5u; ++i)
        originalBytes[i] = p[i];

    const unsigned long currentTarget = ResolveRelativeCallTargetA4(callSite);
    if (!currentTarget || !IsExecutableAddress(reinterpret_cast<const void*>(currentTarget)))
    {
        return false;
    }

    *chained = reinterpret_cast<PausePopulate_t>(currentTarget);

    if (!PatchRelativeCallDirect(callSite, hook))
    {
        *chained = 0;
        return false;
    }

    *installed = true;
    return true;
}

static bool InstallPauseMenuHook()
{

    const bool a = InstallOnePausePopulationHook(
        kPausePopulateCallA,
        reinterpret_cast<void*>(&NFSMW_PhotoMode_PausePopulateHookA),
        &gChainedPausePopulateA, gPausePopulateOriginalA,
        &gPausePopulateHookAInstalled);

    const bool b = InstallOnePausePopulationHook(
        kPausePopulateCallB,
        reinterpret_cast<void*>(&NFSMW_PhotoMode_PausePopulateHookB),
        &gChainedPausePopulateB, gPausePopulateOriginalB,
        &gPausePopulateHookBInstalled);
    return a || b;
}

static void RestoreOnePausePopulationHook(
    unsigned long callSite,
    void* hook,
    const unsigned char originalBytes[5],
    bool* installed)
{
    if (!*installed) return;
    const unsigned long currentTarget = ResolveRelativeCallTargetA4(callSite);
    if (currentTarget == reinterpret_cast<unsigned long>(hook))
        WriteProtected(reinterpret_cast<void*>(callSite), originalBytes, 5u);
    *installed = false;
}

static void RestorePauseMenuHook()
{
    RestoreOnePausePopulationHook(
        kPausePopulateCallA,
        reinterpret_cast<void*>(&NFSMW_PhotoMode_PausePopulateHookA),
        gPausePopulateOriginalA, &gPausePopulateHookAInstalled);
    RestoreOnePausePopulationHook(
        kPausePopulateCallB,
        reinterpret_cast<void*>(&NFSMW_PhotoMode_PausePopulateHookB),
        gPausePopulateOriginalB, &gPausePopulateHookBInstalled);

    gChainedPausePopulateA = 0;
    gChainedPausePopulateB = 0;
    gPauseMenuInjected = 0;
}

static void ReleaseCapturedAudioSessions(bool restorePreviousState)
{
    for (unsigned int i = 0; i < gAudioSessionCount; ++i)
    {
        if (gAudioSessions[i].volume)
        {
            if (restorePreviousState)
                gAudioSessions[i].volume->SetMute(gAudioSessions[i].wasMuted, 0);
            gAudioSessions[i].volume->Release();
            gAudioSessions[i].volume = 0;
        }
        gAudioSessions[i].wasMuted = FALSE;
    }
    gAudioSessionCount = 0;
    gAudioMuteApplied = false;

    if (gAudioComOwned)
    {
        CoUninitialize();
        gAudioComOwned = false;
    }
}

static bool MuteCurrentProcessAudioSessions()
{
    if (gAudioMuteApplied) return true;

    HRESULT initHr = CoInitializeEx(0, COINIT_MULTITHREADED);
    if (initHr == S_OK || initHr == S_FALSE)
    {
        gAudioComOwned = true;
    }
    else if (initHr != RPC_E_CHANGED_MODE)
    {
        return false;
    }

    IMMDeviceEnumerator* deviceEnumerator = 0;
    IMMDeviceCollection* devices = 0;
    HRESULT hr = CoCreateInstance(__uuidof(MMDeviceEnumerator), 0, CLSCTX_ALL,
                                  __uuidof(IMMDeviceEnumerator),
                                  reinterpret_cast<void**>(&deviceEnumerator));
    if (FAILED(hr) || !deviceEnumerator)
    {
        ReleaseCapturedAudioSessions(false);
        return false;
    }

    hr = deviceEnumerator->EnumAudioEndpoints(eRender, DEVICE_STATE_ACTIVE, &devices);
    if (FAILED(hr) || !devices)
    {
        deviceEnumerator->Release();
        ReleaseCapturedAudioSessions(false);
        return false;
    }

    UINT deviceCount = 0;
    devices->GetCount(&deviceCount);
    const DWORD ourPid = GetCurrentProcessId();

    for (UINT d = 0; d < deviceCount && gAudioSessionCount < 16u; ++d)
    {
        IMMDevice* device = 0;
        if (FAILED(devices->Item(d, &device)) || !device) continue;

        IAudioSessionManager2* manager = 0;
        hr = device->Activate(__uuidof(IAudioSessionManager2), CLSCTX_ALL, 0,
                              reinterpret_cast<void**>(&manager));
        if (SUCCEEDED(hr) && manager)
        {
            IAudioSessionEnumerator* sessions = 0;
            if (SUCCEEDED(manager->GetSessionEnumerator(&sessions)) && sessions)
            {
                int count = 0;
                sessions->GetCount(&count);
                for (int i = 0; i < count && gAudioSessionCount < 16u; ++i)
                {
                    IAudioSessionControl* control = 0;
                    if (FAILED(sessions->GetSession(i, &control)) || !control) continue;

                    IAudioSessionControl2* control2 = 0;
                    if (SUCCEEDED(control->QueryInterface(__uuidof(IAudioSessionControl2),
                                                         reinterpret_cast<void**>(&control2))) &&
                        control2)
                    {
                        DWORD pid = 0;
                        if (SUCCEEDED(control2->GetProcessId(&pid)) && pid == ourPid)
                        {
                            ISimpleAudioVolume* volume = 0;
                            if (SUCCEEDED(control->QueryInterface(__uuidof(ISimpleAudioVolume),
                                                                 reinterpret_cast<void**>(&volume))) &&
                                volume)
                            {
                                BOOL wasMuted = FALSE;
                                if (SUCCEEDED(volume->GetMute(&wasMuted)) &&
                                    SUCCEEDED(volume->SetMute(TRUE, 0)))
                                {
                                    gAudioSessions[gAudioSessionCount].volume = volume;
                                    gAudioSessions[gAudioSessionCount].wasMuted = wasMuted;
                                    ++gAudioSessionCount;
                                    volume = 0;
                                }
                                if (volume) volume->Release();
                            }
                        }
                        control2->Release();
                    }
                    control->Release();
                }
                sessions->Release();
            }
            manager->Release();
        }
        device->Release();
    }

    devices->Release();
    deviceEnumerator->Release();

    if (gAudioSessionCount == 0)
    {
        ReleaseCapturedAudioSessions(false);
        return false;
    }

    gAudioMuteApplied = true;
    return true;
}

static void RestoreCurrentProcessAudioSessions()
{
    if (!gAudioMuteApplied && gAudioSessionCount == 0) return;
    ReleaseCapturedAudioSessions(true);
}

static bool HasExpectedHudInstruction()
{
    if (!IsReadableRange(reinterpret_cast<const void*>(kDrawHudInstruction), 12u))
        return false;
    const unsigned char* p = reinterpret_cast<const unsigned char*>(kDrawHudInstruction);
    return p[0] == 0xBDu && p[1] <= 0x01u &&
           p[2] == 0x00u && p[3] == 0x00u && p[4] == 0x00u &&
           p[5] == 0x3Bu && p[6] == 0xC5u &&
           p[7] == 0x0Fu && p[8] == 0x85u;
}

static bool HideGameplayHud()
{
    if (!HasExpectedHudInstruction())
    {
        return false;
    }

    unsigned char* immediate = reinterpret_cast<unsigned char*>(kDrawHudImmediate);
    gSavedDrawHud = *immediate;
    const unsigned char hidden = 0u;
    gHudPatched = WriteProtected(immediate, &hidden, 1u);
    return gHudPatched;
}

static void EnforceGameplayHudHidden()
{
    if (!gHudPatched) return;
    unsigned char* immediate = reinterpret_cast<unsigned char*>(kDrawHudImmediate);
    if (*immediate != 0u)
    {
        const unsigned char hidden = 0u;
        WriteProtected(immediate, &hidden, 1u);
    }
}

static void RestoreGameplayHud()
{
    if (!gHudPatched) return;
    WriteProtected(reinterpret_cast<void*>(kDrawHudImmediate), &gSavedDrawHud, 1u);
    gHudPatched = false;
}

static void ApplyPhotoState()
{
    if (gPhotoStateApplied) return;

    float* gameSpeed = reinterpret_cast<float*>(kTweakGameSpeed);
    gSavedGameSpeed = *gameSpeed;

    HideGameplayHud();

    MuteCurrentProcessAudioSessions();

    gPhotoStateApplied = true;
    gWorldFrozen = false;
    gFreezePending = true;
    gHudHideTick = GetTickCount();
}

static void TryFreezeWorldAfterHudPropagation()
{
    if (!gPhotoStateApplied || !gFreezePending || gWorldFrozen)
        return;

    EnforceGameplayHudHidden();

    const DWORD now = GetTickCount();
    if ((now - gHudHideTick) < kHudPropagationDelayMs)
        return;

    const float frozen = 0.0f;
    if (WriteProtected(reinterpret_cast<void*>(kTweakGameSpeed), &frozen, sizeof(frozen)))
    {
        gWorldFrozen = true;
        gFreezePending = false;
    }
    else
    {
    }
}

static void RestorePhotoState()
{
    if (!gPhotoStateApplied) return;

    RestoreGameplayHud();
    WriteProtected(reinterpret_cast<void*>(kTweakGameSpeed),
                   &gSavedGameSpeed, sizeof(gSavedGameSpeed));
    RestoreCurrentProcessAudioSessions();

    gFreezePending = false;
    gWorldFrozen = false;
    gHudHideTick = 0;
    gPhotoStateApplied = false;
}

static void InitializeOrbitFromGameplay(const Vec3& eye, const Vec3& target)
{
    Vec3 d;
    d.x = eye.x - target.x;
    d.y = eye.y - target.y;
    d.z = eye.z - target.z;

    const float horizontal = sqrtf(d.x * d.x + d.y * d.y);
    const float length = VecLength(d);

    if (length > 0.25f && length < 100.0f)
    {
        gYaw = atan2f(d.y, d.x);
        gPitch = atan2f(d.z, horizontal > 0.001f ? horizontal : 0.001f);
        gDistance = ClampFloat(length, 4.65f, 6.65f);
    }
    else
    {
        gYaw = 0.0f;
        gPitch = 0.20f;
        gDistance = 5.5f;
    }

    const float kMinPitch = 0.07853982f;
    const float kMaxPitch = 0.34906585f;
    gPitch = ClampFloat(gPitch, kMinPitch, kMaxPitch);

    gOrbitInitialized = true;
    gLastOrbitTick = GetTickCount();
}

static void UpdateOrbitInput()
{
    DWORD now = GetTickCount();
    float dt = 0.0f;
    if (gLastOrbitTick != 0)
    {
        DWORD elapsed = now - gLastOrbitTick;
        dt = (float)elapsed * 0.001f;
        if (dt > 0.05f) dt = 0.05f;
    }
    gLastOrbitTick = now;

    if (dt <= 0.0f) return;

    const float rotateSpeed = 1.65f;
    const float pitchSpeed  = 0.75f;
    const float zoomSpeed   = 2.5f;

    if (IsKeyDown(VK_LEFT))  gYaw -= rotateSpeed * dt;
    if (IsKeyDown(VK_RIGHT)) gYaw += rotateSpeed * dt;
    if (IsKeyDown(VK_UP))    gPitch += pitchSpeed * dt;
    if (IsKeyDown(VK_DOWN))  gPitch -= pitchSpeed * dt;

    if (IsKeyDown(VK_9) || IsKeyDown(VK_NUMPAD9)) gDistance += zoomSpeed * dt;
    if (IsKeyDown(VK_0) || IsKeyDown(VK_NUMPAD0)) gDistance -= zoomSpeed * dt;

    const float kMinPitch = 0.07853982f;
    const float kMaxPitch = 0.34906585f;
    gPitch = ClampFloat(gPitch, kMinPitch, kMaxPitch);
    gDistance = ClampFloat(gDistance, 4.65f, 6.65f);
}

static Vec3 BuildOrbitEye(const Vec3& target)
{
    const float cp = cosf(gPitch);
    const float sp = sinf(gPitch);
    const float cy = cosf(gYaw);
    const float sy = sinf(gYaw);

    Vec3 eye;
    eye.x = target.x + gDistance * cp * cy;
    eye.y = target.y + gDistance * cp * sy;
    eye.z = target.z + gDistance * sp;
    return eye;
}

extern "C" __declspec(noinline) void __cdecl NFSMW_PhotoMode_LookAtHook(
    Mat4* out, const Vec3* eye, const Vec3* target, const Vec3* up)
{
    CreateLookAt_t original = gChainedLookAt;
    if (!original)
        original = reinterpret_cast<CreateLookAt_t>(kCreateLookAt);
if (!gPhotoActive &&
        InterlockedCompareExchange(&gPausePhotoRequested, 0, 0) != 0 &&
        ReasonableVec(eye) && ReasonableVec(target) && ReasonableVec(up))
    {
        const DWORD now = GetTickCount();
        if ((now - gPausePhotoRequestTick) >= kPauseToPhotoDelayMs)
        {
            InterlockedExchange(&gPausePhotoRequested, 0);
            gPhotoActive = true;
            gOrbitInitialized = false;
            gLastOrbitTick = 0;
            ApplyPhotoState();
        }
    }

    const bool f8 = IsKeyDown(VK_F8);
    if (f8 && !gF8WasDown)
    {
        InterlockedExchange(&gPausePhotoRequested, 0);
        gPhotoActive = !gPhotoActive;
        gOrbitInitialized = false;
        gLastOrbitTick = 0;

        if (gPhotoActive)
        {
            ApplyPhotoState();
        }
        else
        {
            RestorePhotoState();
        }
    }
    gF8WasDown = f8;

    const bool esc = IsKeyDown(VK_ESCAPE);
    if (gPhotoActive && esc && !gEscWasDown)
    {
        gPhotoActive = false;
        gOrbitInitialized = false;
        gLastOrbitTick = 0;
        RestorePhotoState();
    }
    gEscWasDown = esc;

    if (!gPhotoActive || !ReasonableVec(eye) || !ReasonableVec(target) || !ReasonableVec(up))
    {
        original(out, eye, target, up);
        return;
    }

    EnforceGameplayHudHidden();
    TryFreezeWorldAfterHudPropagation();

    if (!gOrbitInitialized)
    {
        InitializeOrbitFromGameplay(*eye, *target);
    }

    UpdateOrbitInput();

    const Vec3 orbitEye = BuildOrbitEye(*target);
    original(out, &orbitEye, target, up);
}

static bool PatchRelativeCall(unsigned long address, void* destination)
{
    unsigned char* p = reinterpret_cast<unsigned char*>(address);
    if (p[0] != 0xE8) return false;

    DWORD oldProtect = 0;
    if (!VirtualProtect(p, 5, PAGE_EXECUTE_READWRITE, &oldProtect)) return false;

    const long rel = static_cast<long>(
        reinterpret_cast<unsigned long>(destination) - (address + 5u));
    p[0] = 0xE8;
    *reinterpret_cast<long*>(p + 1) = rel;

    DWORD ignored = 0;
    VirtualProtect(p, 5, oldProtect, &ignored);
    FlushInstructionCache(GetCurrentProcess(), p, 5);
    return true;
}

static unsigned long ResolveRelativeCallTarget(unsigned long address)
{
    const unsigned char* p = reinterpret_cast<const unsigned char*>(address);
    if (p[0] != 0xE8) return 0;
    const long rel = *reinterpret_cast<const long*>(p + 1);
    return address + 5u + rel;
}

static bool PrepareChainSafeHook()
{
    static const unsigned char lookAtFn[6]         = { 0x55, 0x8B, 0xEC, 0x83, 0xE4, 0xF0 };

    const unsigned char* callSite = reinterpret_cast<const unsigned char*>(kLookAtCallSite);
    const bool retailFn   = BytesEqual(reinterpret_cast<const unsigned char*>(kCreateLookAt),
                                       lookAtFn, 6);
    if (!retailFn)
    {
        return false;
    }

    if (callSite[0] != 0xE8)
    {
        return false;
    }

    const unsigned long currentTarget = ResolveRelativeCallTarget(kLookAtCallSite);
    if (!currentTarget)
    {
        return false;
    }

    if (currentTarget == reinterpret_cast<unsigned long>(&NFSMW_PhotoMode_LookAtHook))
    {
        return false;
    }

    gChainedLookAt = reinterpret_cast<CreateLookAt_t>(currentTarget);
return true;
}

struct OverlayVertex
{
    float x, y, z, rhw;
    D3DCOLOR color;
};

static const DWORD kOverlayFVF = D3DFVF_XYZRHW | D3DFVF_DIFFUSE;
static OverlayVertex gOverlayBatch[12288];
static unsigned int gOverlayBatchCount = 0;

static void BatchVertex(float x, float y, D3DCOLOR color)
{
    if (gOverlayBatchCount >= (sizeof(gOverlayBatch) / sizeof(gOverlayBatch[0]))) return;
    OverlayVertex& v = gOverlayBatch[gOverlayBatchCount++];
    v.x = x; v.y = y; v.z = 0.0f; v.rhw = 1.0f; v.color = color;
}

static void BatchRect(float x0, float y0, float x1, float y1, D3DCOLOR color)
{
    BatchVertex(x0, y0, color); BatchVertex(x1, y0, color); BatchVertex(x0, y1, color);
    BatchVertex(x0, y1, color); BatchVertex(x1, y0, color); BatchVertex(x1, y1, color);
}

static void BatchTri(float x0, float y0, float x1, float y1, float x2, float y2, D3DCOLOR color)
{
    BatchVertex(x0, y0, color); BatchVertex(x1, y1, color); BatchVertex(x2, y2, color);
}

static const unsigned char* Glyph(char c)
{
    static const unsigned char glyphs[36][7] = {
        {0x0E,0x11,0x11,0x1F,0x11,0x11,0x11},
        {0x1E,0x11,0x11,0x1E,0x11,0x11,0x1E},
        {0x0F,0x10,0x10,0x10,0x10,0x10,0x0F},
        {0x1E,0x11,0x11,0x11,0x11,0x11,0x1E},
        {0x1F,0x10,0x10,0x1E,0x10,0x10,0x1F},
        {0x1F,0x10,0x10,0x1E,0x10,0x10,0x10},
        {0x0F,0x10,0x10,0x17,0x11,0x11,0x0F},
        {0x11,0x11,0x11,0x1F,0x11,0x11,0x11},
        {0x0E,0x04,0x04,0x04,0x04,0x04,0x0E},
        {0x07,0x02,0x02,0x02,0x12,0x12,0x0C},
        {0x11,0x12,0x14,0x18,0x14,0x12,0x11},
        {0x10,0x10,0x10,0x10,0x10,0x10,0x1F},
        {0x11,0x1B,0x15,0x15,0x11,0x11,0x11},
        {0x11,0x19,0x15,0x13,0x11,0x11,0x11},
        {0x0E,0x11,0x11,0x11,0x11,0x11,0x0E},
        {0x1E,0x11,0x11,0x1E,0x10,0x10,0x10},
        {0x0E,0x11,0x11,0x11,0x15,0x12,0x0D},
        {0x1E,0x11,0x11,0x1E,0x14,0x12,0x11},
        {0x0F,0x10,0x10,0x0E,0x01,0x01,0x1E},
        {0x1F,0x04,0x04,0x04,0x04,0x04,0x04},
        {0x11,0x11,0x11,0x11,0x11,0x11,0x0E},
        {0x11,0x11,0x11,0x11,0x11,0x0A,0x04},
        {0x11,0x11,0x11,0x15,0x15,0x15,0x0A},
        {0x11,0x11,0x0A,0x04,0x0A,0x11,0x11},
        {0x11,0x11,0x0A,0x04,0x04,0x04,0x04},
        {0x1F,0x01,0x02,0x04,0x08,0x10,0x1F},
        {0x0E,0x11,0x13,0x15,0x19,0x11,0x0E},
        {0x04,0x0C,0x04,0x04,0x04,0x04,0x0E},
        {0x0E,0x11,0x01,0x02,0x04,0x08,0x1F},
        {0x1E,0x01,0x01,0x0E,0x01,0x01,0x1E},
        {0x02,0x06,0x0A,0x12,0x1F,0x02,0x02},
        {0x1F,0x10,0x10,0x1E,0x01,0x01,0x1E},
        {0x0E,0x10,0x10,0x1E,0x11,0x11,0x0E},
        {0x1F,0x01,0x02,0x04,0x08,0x08,0x08},
        {0x0E,0x11,0x11,0x0E,0x11,0x11,0x0E},
        {0x0E,0x11,0x11,0x0F,0x01,0x01,0x0E}
    };

    if (c >= 'a' && c <= 'z') c = char(c - 'a' + 'A');
    if (c >= 'A' && c <= 'Z') return glyphs[c - 'A'];
    if (c >= '0' && c <= '9') return glyphs[26 + (c - '0')];
    return 0;
}

static float TextWidth(const char* text, float px)
{
    if (!text) return 0.0f;
    float w = 0.0f;
    for (unsigned int i = 0; text[i]; ++i)
        w += (text[i] == ' ') ? (4.0f * px) : (6.0f * px);
    return w;
}

static void BatchTextRaw(float x, float y, const char* text, float px, D3DCOLOR color)
{
    if (!text) return;
    for (unsigned int n = 0; text[n]; ++n)
    {
        const char c = text[n];
        if (c == ' ')
        {
            x += 4.0f * px;
            continue;
        }

        const unsigned char* rows = Glyph(c);
        if (rows)
        {
            for (int row = 0; row < 7; ++row)
            {
                for (int col = 0; col < 5; ++col)
                {
                    if (rows[row] & (1u << (4 - col)))
                    {
                        const float x0 = x + col * px;
                        const float y0 = y + row * px;
                        BatchRect(x0, y0, x0 + px, y0 + px, color);
                    }
                }
            }
        }
        x += 6.0f * px;
    }
}

static void BatchText(float x, float y, const char* text, float px, D3DCOLOR color)
{
    BatchTextRaw(x + px * 0.65f, y + px * 0.65f, text, px, D3DCOLOR_ARGB(190,0,0,0));
    BatchTextRaw(x, y, text, px, color);
}

static void BatchOutlineRect(float x0, float y0, float x1, float y1,
                             float t, D3DCOLOR border, D3DCOLOR fill)
{
    BatchRect(x0, y0, x1, y1, fill);
    BatchRect(x0, y0, x1, y0+t, border);
    BatchRect(x0, y1-t, x1, y1, border);
    BatchRect(x0, y0, x0+t, y1, border);
    BatchRect(x1-t, y0, x1, y1, border);
}

static void BatchKeyBox(float x, float y, float w, float h, const char* key, float px)
{
    const D3DCOLOR white = D3DCOLOR_ARGB(235,245,245,245);
    BatchOutlineRect(x,y,x+w,y+h,2.0f,white,D3DCOLOR_ARGB(155,5,5,5));
    const float tw = TextWidth(key, px);
    const float th = 7.0f * px;
    BatchText(x + (w-tw)*0.5f, y + (h-th)*0.5f, key, px, white);
}

static void BatchArrowBox(float x, float y, float s, int dir)
{
    const D3DCOLOR white = D3DCOLOR_ARGB(235,245,245,245);
    BatchOutlineRect(x,y,x+s,y+s,2.0f,white,D3DCOLOR_ARGB(155,5,5,5));
    const float cx=x+s*0.5f, cy=y+s*0.5f, a=s*0.22f;
    if (dir==0) BatchTri(cx,cy-a, cx-a,cy+a, cx+a,cy+a, white);
    if (dir==1) BatchTri(cx,cy+a, cx-a,cy-a, cx+a,cy-a, white);
    if (dir==2) BatchTri(cx-a,cy, cx+a,cy-a, cx+a,cy+a, white);
    if (dir==3) BatchTri(cx+a,cy, cx-a,cy-a, cx-a,cy+a, white);
}

static void DrawGradientQuad(IDirect3DDevice9* dev,
                             float x0,float y0,float x1,float y1,
                             D3DCOLOR cTL,D3DCOLOR cTR,D3DCOLOR cBL,D3DCOLOR cBR)
{
    OverlayVertex v[4];
    v[0].x=x0; v[0].y=y0; v[0].z=0; v[0].rhw=1; v[0].color=cTL;
    v[1].x=x1; v[1].y=y0; v[1].z=0; v[1].rhw=1; v[1].color=cTR;
    v[2].x=x0; v[2].y=y1; v[2].z=0; v[2].rhw=1; v[2].color=cBL;
    v[3].x=x1; v[3].y=y1; v[3].z=0; v[3].rhw=1; v[3].color=cBR;
    dev->DrawPrimitiveUP(D3DPT_TRIANGLESTRIP,2,v,sizeof(OverlayVertex));
}

static void DrawPhotoOverlay(IDirect3DDevice9* dev)
{
    if (!dev || !gPhotoActive) return;

    IDirect3DStateBlock9* state = 0;
    if (SUCCEEDED(dev->CreateStateBlock(D3DSBT_ALL, &state)) && state)
        state->Capture();

    dev->SetVertexShader(0);
    dev->SetPixelShader(0);
    dev->SetTexture(0,0);
    dev->SetFVF(kOverlayFVF);
    dev->SetRenderState(D3DRS_ZENABLE, FALSE);
    dev->SetRenderState(D3DRS_ZWRITEENABLE, FALSE);
    dev->SetRenderState(D3DRS_CULLMODE, D3DCULL_NONE);
    dev->SetRenderState(D3DRS_ALPHABLENDENABLE, TRUE);
    dev->SetRenderState(D3DRS_SRCBLEND, D3DBLEND_SRCALPHA);
    dev->SetRenderState(D3DRS_DESTBLEND, D3DBLEND_INVSRCALPHA);
    dev->SetRenderState(D3DRS_LIGHTING, FALSE);
    dev->SetRenderState(D3DRS_FOGENABLE, FALSE);
    dev->SetTextureStageState(0,D3DTSS_COLOROP,D3DTOP_SELECTARG1);
    dev->SetTextureStageState(0,D3DTSS_COLORARG1,D3DTA_DIFFUSE);
    dev->SetTextureStageState(0,D3DTSS_ALPHAOP,D3DTOP_SELECTARG1);
    dev->SetTextureStageState(0,D3DTSS_ALPHAARG1,D3DTA_DIFFUSE);

    D3DVIEWPORT9 vp;
    if (SUCCEEDED(dev->GetViewport(&vp)))
    {
        const float w=(float)vp.Width, h=(float)vp.Height;
        const float edgeW=w*0.18f, edgeH=h*0.16f, bottomH=h*0.22f;
        const D3DCOLOR blackStrong=D3DCOLOR_ARGB(195,0,0,0);
        const D3DCOLOR blackMid=D3DCOLOR_ARGB(130,0,0,0);
        const D3DCOLOR clear=D3DCOLOR_ARGB(0,0,0,0);

        DrawGradientQuad(dev,0,0,edgeW,h,blackStrong,clear,blackStrong,clear);
        DrawGradientQuad(dev,w-edgeW,0,w,h,clear,blackStrong,clear,blackStrong);
        DrawGradientQuad(dev,0,0,w,edgeH,blackMid,blackMid,clear,clear);
        DrawGradientQuad(dev,0,h-bottomH,w,h,clear,clear,blackStrong,blackStrong);

        gOverlayBatchCount=0;
        const float scale=(h/720.0f < 0.82f) ? 0.82f : (h/720.0f);
        const float px=2.0f*scale;
        const float boxH=31.0f*scale;
        const float y=h-58.0f*scale;
        const D3DCOLOR white=D3DCOLOR_ARGB(240,245,245,245);

        const float left=w*0.155f;
        BatchKeyBox(left,y,52.0f*scale,boxH,"ESC",px);
        BatchText(left+61.0f*scale,y+8.0f*scale,"BACK",px,white);

        const float center=w*0.45f;
        BatchKeyBox(center,y,28.0f*scale,boxH,"9",px);
        BatchKeyBox(center+32.0f*scale,y,28.0f*scale,boxH,"0",px);
        BatchText(center+69.0f*scale,y+8.0f*scale,"ZOOM",px,white);

        const float right=w*0.64f;
        const float as=28.0f*scale;
        BatchArrowBox(right,y,as,0);
        BatchArrowBox(right+32.0f*scale,y,as,1);
        BatchArrowBox(right+64.0f*scale,y,as,2);
        BatchArrowBox(right+96.0f*scale,y,as,3);
        BatchText(right+133.0f*scale,y+8.0f*scale,"VIEW CAR",px,white);

        if (gOverlayBatchCount)
            dev->DrawPrimitiveUP(D3DPT_TRIANGLELIST,gOverlayBatchCount/3,
                                 gOverlayBatch,sizeof(OverlayVertex));
    }

    if (state)
    {
        state->Apply();
        state->Release();
    }
}

static HRESULT WINAPI NFSMW_PhotoMode_PresentHook(
    IDirect3DDevice9* dev,
    const RECT* sourceRect,
    const RECT* destRect,
    HWND destWindowOverride,
    const RGNDATA* dirtyRegion)
{
    if (gPhotoActive && dev)
    {
        const HRESULT beginResult = dev->BeginScene();
        if (SUCCEEDED(beginResult))
        {
            DrawPhotoOverlay(dev);
            dev->EndScene();
        }
    }

    Present_t original = gChainedPresent;
    return original ? original(dev, sourceRect, destRect, destWindowOverride, dirtyRegion) : D3D_OK;
}

static bool InstallOrRefreshOverlayHook()
{
    if (!IsReadableRange(reinterpret_cast<const void*>(kD3DDevicePtr), 4)) return false;

    IDirect3DDevice9* dev = *reinterpret_cast<IDirect3DDevice9**>(kD3DDevicePtr);
    if (!dev || !IsReadableRange(dev, sizeof(void*))) return false;

    void** vtbl = *reinterpret_cast<void***>(dev);
    if (!vtbl || !IsReadableRange(vtbl, 18u * sizeof(void*))) return false;

    void** slot = &vtbl[17];
    Present_t current = reinterpret_cast<Present_t>(*slot);
    if (!current) return false;

    if (current == &NFSMW_PhotoMode_PresentHook)
    {
        gPresentSlot = slot;
        gOverlayHookInstalled = true;
        return true;
    }

    if (!IsExecutableAddress(reinterpret_cast<void*>(current))) return false;

    DWORD oldProtect = 0;
    if (!VirtualProtect(slot, sizeof(void*), PAGE_EXECUTE_READWRITE, &oldProtect))
        return false;

    gChainedPresent = current;
    gPresentSlot = slot;
    *slot = reinterpret_cast<void*>(&NFSMW_PhotoMode_PresentHook);

    DWORD ignored = 0;
    VirtualProtect(slot, sizeof(void*), oldProtect, &ignored);
    FlushInstructionCache(GetCurrentProcess(), slot, sizeof(void*));
    gOverlayHookInstalled = true;
    return true;
}

static void RestoreOverlayHook()
{
    if (!gPresentSlot || !gChainedPresent) return;
    if (!IsReadableRange(gPresentSlot, sizeof(void*))) return;
    if (*gPresentSlot != reinterpret_cast<void*>(&NFSMW_PhotoMode_PresentHook)) return;

    DWORD oldProtect = 0;
    if (!VirtualProtect(gPresentSlot, sizeof(void*), PAGE_EXECUTE_READWRITE, &oldProtect))
        return;

    *gPresentSlot = reinterpret_cast<void*>(gChainedPresent);
    DWORD ignored = 0;
    VirtualProtect(gPresentSlot, sizeof(void*), oldProtect, &ignored);
    FlushInstructionCache(GetCurrentProcess(), gPresentSlot, sizeof(void*));
}

static DWORD WINAPI OverlayHookThread(LPVOID)
{
    while (InterlockedCompareExchange(&gShutdown, 0, 0) == 0)
    {
        InstallOrRefreshOverlayHook();

        Sleep(gOverlayHookInstalled ? 500 : 100);
    }
    return 0;
}

static bool Install()
{
    if (!PrepareChainSafeHook())
    {
        MessageBoxA(0,
            "This script couldn't be loaded.\n"
            "Another camera mod may be using an incompatible hook at the same call site.",
            "Error",
            MB_OK | MB_ICONERROR | MB_TOPMOST);
        return false;
    }

    if (!PatchRelativeCall(kLookAtCallSite,
        reinterpret_cast<void*>(&NFSMW_PhotoMode_LookAtHook)))
    {
        return false;
    }
    InstallLocalizationHook();
    InstallPauseMenuHook();
    HANDLE overlayThread = CreateThread(0, 0, &OverlayHookThread, 0, 0, 0);
    if (overlayThread)
        CloseHandle(overlayThread);

    return true;
}

BOOL APIENTRY DllMain(HMODULE hModule, DWORD reason, LPVOID)
{
    if (reason == DLL_PROCESS_ATTACH)
    {
        DisableThreadLibraryCalls(hModule);
        Install();
    }
    else if (reason == DLL_PROCESS_DETACH)
    {
        InterlockedExchange(&gShutdown,1);
        RestorePhotoState();
        RestorePauseMenuHook();
        RestoreLocalizationHook();
        RestoreOverlayHook();
    }
    return TRUE;
}
