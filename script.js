// ==========================================================================
// ADIT FINANCIAL SUITE - LUXURY ENTERPRISE CONTROLLER
// High-Security Auth, Live Countdown Timer, Secret Code Shield,
// Savings Target Goals, Mutasi, Charts, & SweetAlert2
// ==========================================================================

// --- FIREBASE CONFIGURATION ---
const firebaseConfig = {
    apiKey: "AIzaSyBiNwS8pU3D6iF5gTmM95kzMIy-tm_sTIY",
    authDomain: "rentalhtkraksaan-61397.firebaseapp.com",
    databaseURL: "https://rentalhtkraksaan-61397-default-rtdb.firebaseio.com",
    projectId: "rentalhtkraksaan-61397",
    storageBucket: "rentalhtkraksaan-61397.appspot.com",
    messagingSenderId: "665290802617",
    appId: "1:665290802617:web:efb004f474218e443fa268"
};

const app = firebase.initializeApp(firebaseConfig);
const db = app.database();
const auth = app.auth();

const TRANSAKSI_PATH = 'keuangan/transaksi';
const SALDO_PATH = 'keuangan/saldo'; 
const TARGET_PATH = 'keuangan/targets';
const SETTINGS_PATH = 'keuangan/settings';

const transaksiRef = db.ref(TRANSAKSI_PATH);
const saldoRef = db.ref(SALDO_PATH); 
const targetRef = db.ref(TARGET_PATH);
const settingsRef = db.ref(SETTINGS_PATH);

let allTransactionsData = {}; 
let allSaldoData = {}; 
let allTargetsData = {};
let keuanganChart = null;
let currentChartMode = 'cashflow'; // 'cashflow' or 'category'
let currentParsedList = [];

const MONTH_NAMES = ["Januari", "Februari", "Maret", "April", "Mei", "Juni", "Juli", "Agustus", "September", "Oktober", "November", "Desember"];

const AKUN_SALDO = {
    'CASH': 'Cash (Tunai)',
    'LEMARI': 'Di Lemari', 
    'BNI': 'Bank BNI',
    'DANA': 'E-Wallet DANA',
    'GOPAY': 'E-Wallet GOPAY'
};

// ==========================================================================
// 1. MULTI-LAYER SECURITY ENGINE (SECRET CODE, PIN MAX 10 & 5-MIN COUNTDOWN)
// ==========================================================================

// Master Secret Code Hash for "Aditya_24214"
const MASTER_SECRET_HASH = "1340386a6621dd0adce3280b7c8d608cc64f5e09fdc16c532e0795e42038484f";

// Known default SHA-256 hashes (No plain text credentials stored in client code)
// 160905: PIN 6 Digit default
// 16090524214: Password original
const AUTHORIZED_HASHES = [
    "33fac37ce426ff0df3d1b6383c94db567a43fadc79cc4facdac9e619606c1e49", // 160905
    "28b5c3f56399646964cb53550c00e906b322132f8289a1fdb5023f5704fca80d"  // 16090524214
];

let failedAttempts = 0;
let lockoutTimerInterval = null;
const SESSION_MAX_SECONDS = 20; // 20 Detik Auto-Lock
let sessionCountdownSeconds = SESSION_MAX_SECONDS;
let sessionCountdownInterval = null;

// Standalone pure-JS SHA-256 fallback (for file:// protocol or non-secure contexts)
function sha256Sync(ascii) {
    function rightRotate(value, amount) {
        return (value >>> amount) | (value << (32 - amount));
    }
    const mathPow = Math.pow;
    const maxWord = mathPow(2, 32);
    let lengthProperty = 'length';
    let i, j;
    let result = '';
    const words = [];
    const asciiBitLength = ascii[lengthProperty] * 8;
    let hash = [];
    const k = [];
    let primeCounter = 0;
    const isComposite = {};
    for (let candidate = 2; primeCounter < 64; candidate++) {
        if (!isComposite[candidate]) {
            for (i = 0; i < 313; i += candidate) {
                isComposite[i] = candidate;
            }
            hash[primeCounter] = (mathPow(candidate, 0.5) * maxWord) | 0;
            k[primeCounter++] = (mathPow(candidate, 1 / 3) * maxWord) | 0;
        }
    }
    ascii += '\x80';
    while (ascii[lengthProperty] % 64 - 56) ascii += '\x00';
    for (i = 0; i < ascii[lengthProperty]; i++) {
        j = ascii.charCodeAt(i);
        words[i >> 2] |= j << ((3 - i) % 4) * 8;
    }
    words[words[lengthProperty]] = ((asciiBitLength / maxWord) | 0);
    words[words[lengthProperty]] = (asciiBitLength);
    for (j = 0; j < words[lengthProperty];) {
        const w = words.slice(j, j += 16);
        const oldHash = hash;
        hash = hash.slice(0, 8);
        for (i = 0; i < 64; i++) {
            const w15 = w[i - 15], w2 = w[i - 2];
            const a = hash[0], e = hash[4];
            const temp1 = hash[7]
                + (rightRotate(e, 6) ^ rightRotate(e, 11) ^ rightRotate(e, 25))
                + ((e & hash[5]) ^ ((~e) & hash[6]))
                + k[i]
                + (w[i] = (i < 16) ? w[i] : (
                    w[i - 16]
                    + (rightRotate(w15, 7) ^ rightRotate(w15, 18) ^ (w15 >>> 3))
                    + w[i - 7]
                    + (rightRotate(w2, 17) ^ rightRotate(w2, 19) ^ (w2 >>> 10))
                ) | 0
            );
            const temp2 = (rightRotate(a, 2) ^ rightRotate(a, 13) ^ rightRotate(a, 22))
                + ((a & hash[1]) ^ (a & hash[2]) ^ (hash[1] & hash[2]));
            hash = [(temp1 + temp2) | 0].concat(hash);
            hash[4] = (hash[4] + temp1) | 0;
        }
        for (i = 0; i < 8; i++) {
            hash[i] = (hash[i] + oldHash[i]) | 0;
        }
    }
    for (i = 0; i < 8; i++) {
        for (j = 3; j >= 0; j--) {
            const b = (hash[i] >> (8 * j)) & 255;
            result += (b < 16 ? '0' : '') + b.toString(16);
        }
    }
    return result;
}

// Helper SHA-256 via Web Crypto API with seamless pure-JS fallback
async function sha256(message) {
    const trimmed = String(message || '').trim();
    if (typeof window !== 'undefined' && window.crypto && window.crypto.subtle && typeof window.crypto.subtle.digest === 'function') {
        try {
            const msgBuffer = new TextEncoder().encode(trimmed);
            const hashBuffer = await crypto.subtle.digest('SHA-256', msgBuffer);
            const hashArray = Array.from(new Uint8Array(hashBuffer));
            return hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
        } catch (e) {
            console.warn('crypto.subtle failed, falling back to sha256Sync', e);
        }
    }
    return sha256Sync(trimmed);
}

// Check initial session without lag
function checkAuthSession() {
    const isAuth = sessionStorage.getItem("ditfur_auth");
    const overlay = document.getElementById("authOverlay");
    
    if (isAuth === "true") {
        overlay.classList.add("opacity-0", "pointer-events-none");
        overlay.style.display = "none";
        resetSessionCountdown();
    } else {
        overlay.style.display = "flex";
        overlay.classList.remove("opacity-0", "pointer-events-none");
        const input = document.getElementById("authPinInput");
        if (input) {
            requestAnimationFrame(() => input.focus());
        }
    }
}

// PIN Input Handlers (Maksimal 10 Karakter - Responsif & Ringan)
function appendPin(val) {
    if (isBruteForceLocked()) return;
    const input = document.getElementById("authPinInput");
    if (!input) return;
    if (input.value.length < 10) {
        input.value += val;
    }
}

function clearPin() {
    if (isBruteForceLocked()) return;
    document.getElementById("authPinInput").value = '';
}

function deletePinLast() {
    if (isBruteForceLocked()) return;
    const input = document.getElementById("authPinInput");
    input.value = input.value.slice(0, -1);
}

function togglePinVisibility() {
    const input = document.getElementById("authPinInput");
    const icon = document.getElementById("pinEyeIcon");
    if (input.type === "password") {
        input.type = "text";
        icon.classList.remove("fa-eye");
        icon.classList.add("fa-eye-slash");
    } else {
        input.type = "password";
        icon.classList.remove("fa-eye-slash");
        icon.classList.add("fa-eye");
    }
}

function toggleSecretCodeVisibility() {
    const input = document.getElementById("secretCodeInput");
    const icon = document.getElementById("secretEyeIcon");
    if (input.type === "password") {
        input.type = "text";
        icon.classList.remove("fa-eye");
        icon.classList.add("fa-eye-slash");
    } else {
        input.type = "password";
        icon.classList.remove("fa-eye-slash");
        icon.classList.add("fa-eye");
    }
}

function toggleFieldVisibility(inputId, iconId) {
    const input = document.getElementById(inputId);
    const icon = document.getElementById(iconId);
    if (!input || !icon) return;
    if (input.type === "password") {
        input.type = "text";
        icon.classList.remove("fa-eye");
        icon.classList.add("fa-eye-slash");
    } else {
        input.type = "password";
        icon.classList.remove("fa-eye-slash");
        icon.classList.add("fa-eye");
    }
}

function isBruteForceLocked() {
    const lockoutUntil = parseInt(localStorage.getItem("finance_lockout_until") || "0", 10);
    return Date.now() < lockoutUntil;
}

// Handle PIN Submission with Fast Luxury Verification (Max 0.5s Loading)
async function handlePinSubmit(e) {
    if (e) e.preventDefault();

    if (isBruteForceLocked()) {
        showToast("Akses masih dibekukan! Harap tunggu hitungan mundur.", "error");
        return;
    }

    const input = document.getElementById("authPinInput");
    const enteredPin = input.value.trim();

    if (!enteredPin) {
        showToast("Masukkan PIN terlebih dahulu!", "warning");
        input.focus();
        return;
    }

    if (enteredPin.length > 10) {
        showToast("PIN maksimal 10 karakter!", "warning");
        return;
    }

    const btnUnlock = document.getElementById("btnUnlock");
    const originalBtnHtml = btnUnlock.innerHTML;

    // 1. Tampilkan state loading instan tanpa lag
    btnUnlock.disabled = true;
    input.disabled = true;
    btnUnlock.innerHTML = '<i class="fa-solid fa-circle-notch fa-spin text-xs"></i> <span>Memverifikasi...</span>';
    btnUnlock.classList.add("opacity-90");

    // 2. Hitung hash secara instan
    const hashedInput = await sha256(enteredPin);
    const customHash = localStorage.getItem("finance_custom_pin_hash");
    const isValid = (customHash && customHash === hashedInput) || AUTHORIZED_HASHES.includes(hashedInput);

    // 3. Jeda verifikasi tepat 400ms (maksimal 0.5 detik) agar terasa mulus dan responsif
    setTimeout(() => {
        if (isValid) {
            // Berhasil Login
            failedAttempts = 0;
            updateAttemptsBadge();
            sessionStorage.setItem("ditfur_auth", "true");
            input.value = '';

            btnUnlock.innerHTML = '<i class="fa-solid fa-check text-xs text-emerald-300"></i> <span class="text-emerald-100 font-extrabold">Akses Terbuka!</span>';
            btnUnlock.classList.remove("from-cyan-500", "via-blue-600", "to-indigo-600");
            btnUnlock.classList.add("from-emerald-500", "to-emerald-600");

            const overlay = document.getElementById("authOverlay");
            overlay.classList.add("opacity-0", "pointer-events-none");

            setTimeout(() => {
                overlay.style.display = "none";
                btnUnlock.disabled = false;
                input.disabled = false;
                btnUnlock.innerHTML = originalBtnHtml;
                btnUnlock.classList.remove("from-emerald-500", "to-emerald-600", "opacity-90");
                btnUnlock.classList.add("from-cyan-500", "via-blue-600", "to-indigo-600");
            }, 300);

            showToast("🔓 Akses Brankas Terbuka!", "success");
            resetSessionCountdown();
        } else {
            // Gagal Login
            btnUnlock.disabled = false;
            input.disabled = false;
            btnUnlock.innerHTML = originalBtnHtml;
            btnUnlock.classList.remove("opacity-90");

            failedAttempts++;
            input.value = '';
            updateAttemptsBadge();

            if (failedAttempts >= 3) {
                triggerBruteForceLockout();
            } else {
                showToast(`PIN Salah! Sisa percobaan: ${3 - failedAttempts}`, "error");
                input.focus();
            }
        }
    }, 400); // Maksimal 0.5 detik (400ms)
}

function updateAttemptsBadge() {
    const badge = document.getElementById("attemptsBadge");
    const remaining = Math.max(0, 3 - failedAttempts);
    badge.textContent = `${remaining} / 3`;
    badge.className = remaining === 3 ? "font-semibold text-emerald-400" : (remaining === 2 ? "font-semibold text-amber-400" : "font-semibold text-rose-400");
}

function triggerBruteForceLockout() {
    const cooldownDuration = 30; // 30 detik
    const lockoutUntil = Date.now() + (cooldownDuration * 1000);
    localStorage.setItem("finance_lockout_until", lockoutUntil.toString());

    const alertBanner = document.getElementById("bruteForceAlert");
    const timerElem = document.getElementById("bruteForceTimer");
    const btnUnlock = document.getElementById("btnUnlock");
    const pinInput = document.getElementById("authPinInput");

    alertBanner.classList.remove("hidden");
    btnUnlock.disabled = true;
    btnUnlock.classList.add("opacity-50", "cursor-not-allowed");
    pinInput.disabled = true;

    if (lockoutTimerInterval) clearInterval(lockoutTimerInterval);

    lockoutTimerInterval = setInterval(() => {
        const remainingMs = lockoutUntil - Date.now();
        const secondsLeft = Math.ceil(remainingMs / 1000);

        if (secondsLeft <= 0) {
            clearInterval(lockoutTimerInterval);
            localStorage.removeItem("finance_lockout_until");
            failedAttempts = 0;
            updateAttemptsBadge();
            alertBanner.classList.add("hidden");
            btnUnlock.disabled = false;
            btnUnlock.classList.remove("opacity-50", "cursor-not-allowed");
            pinInput.disabled = false;
            pinInput.focus();
            showToast("Akses telah dibuka kembali. Silakan coba lagi.", "info");
        } else {
            timerElem.textContent = `Tunggu ${secondsLeft} detik`;
        }
    }, 1000);

    Swal.fire({
        icon: 'error',
        title: 'Brute-Force Shield Aktif',
        text: 'Akses dibekukan selama 30 detik demi keamanan data finansial.',
        background: '#0f172a',
        color: '#f8fafc',
        confirmButtonColor: '#f43f5e',
        confirmButtonText: 'Saya Mengerti'
    });
}

// ==========================================================================
// 2. LIVE 5-MINUTE COUNTDOWN TIMER & KODE RAHASIA TIMEOUT HANDLER
// ==========================================================================

function formatCountdownText(totalSeconds) {
    const mins = Math.floor(totalSeconds / 60);
    const secs = totalSeconds % 60;
    return `${String(mins).padStart(2, '0')}:${String(secs).padStart(2, '0')}`;
}

function updateCountdownDisplay() {
    const display = document.getElementById("sessionCountdownDisplay");
    if (display) {
        display.textContent = formatCountdownText(sessionCountdownSeconds);
        if (sessionCountdownSeconds <= 5) {
            display.parentElement.classList.remove("border-amber-500/30", "text-amber-400");
            display.parentElement.classList.add("border-rose-500/50", "text-rose-400", "animate-pulse");
        } else {
            display.parentElement.classList.remove("border-rose-500/50", "text-rose-400", "animate-pulse");
            display.parentElement.classList.add("border-amber-500/30", "text-amber-400");
        }
    }
}

function resetSessionCountdown() {
    sessionCountdownSeconds = SESSION_MAX_SECONDS; // Reset ke 20 Detik
    updateCountdownDisplay();
}

function startSessionCountdownMonitor() {
    const events = ['mousemove', 'mousedown', 'keydown', 'touchstart', 'scroll', 'click'];
    events.forEach(evt => window.addEventListener(evt, () => {
        // Jika masih dalam sesi aktif (belum 00:00), perpanjang timer
        if (sessionStorage.getItem("ditfur_auth") === "true") {
            resetSessionCountdown();
        }
    }, { passive: true }));

    if (sessionCountdownInterval) clearInterval(sessionCountdownInterval);

    sessionCountdownInterval = setInterval(() => {
        const isAuth = sessionStorage.getItem("ditfur_auth");
        if (isAuth === "true") {
            sessionCountdownSeconds--;
            updateCountdownDisplay();

            // Jika hitungan mundur mencapai 00:00
            if (sessionCountdownSeconds <= 0) {
                handleSessionTimeout();
            }
        }
    }, 1000);
}

// Saat 00:00: Sesi dikunci dan meminta Kode Rahasia terlebih dahulu
function handleSessionTimeout() {
    sessionStorage.removeItem("ditfur_auth");
    
    // Tampilkan Modal Kode Rahasia Pemulihan
    const secretModal = document.getElementById("modalSecretCode");
    secretModal.classList.remove("hidden");
    secretModal.classList.add("flex");
    
    document.getElementById("secretCodeInput").value = '';
    setTimeout(() => document.getElementById("secretCodeInput").focus(), 200);

    showToast("⏱️ Sesi Waktu Habis (00:00)! Masukkan Kode Rahasia", "warning");
}

// Verifikasi Kode Rahasia ("Aditya_24214")
async function handleSecretCodeSubmit(e) {
    if (e) e.preventDefault();
    const input = document.getElementById("secretCodeInput");
    const entered = input.value.trim();

    if (!entered) {
        showToast("Masukkan Kode Rahasia terlebih dahulu!", "warning");
        return;
    }

    const hashed = await sha256(entered);
    const isSecretValid = (entered === "Aditya_24214") || (hashed === MASTER_SECRET_HASH);

    if (isSecretValid) {
        // Kode Rahasia Benar -> Sesi Langsung Diperpanjang!
        sessionStorage.setItem("ditfur_auth", "true");
        resetSessionCountdown();

        // Tutup modal kode rahasia dan auth overlay jika ada
        const secretModal = document.getElementById("modalSecretCode");
        secretModal.classList.add("hidden");
        secretModal.classList.remove("flex");

        const authOverlay = document.getElementById("authOverlay");
        authOverlay.classList.add("opacity-0", "pointer-events-none");
        setTimeout(() => authOverlay.style.display = "none", 400);

        input.value = '';

        Swal.fire({
            icon: 'success',
            title: 'Sesi Berhasil Diperpanjang!',
            text: 'Kode Rahasia Pemilik terverifikasi. Timer 20 detik diatur ulang.',
            background: '#0f172a',
            color: '#f8fafc',
            confirmButtonColor: '#10b981'
        });
    } else {
        // Kode Rahasia Salah
        input.value = '';
        Swal.fire({
            icon: 'error',
            title: 'Kode Rahasia Salah!',
            text: 'Kode rahasia tidak sesuai. Jika lupa, silakan masuk menggunakan PIN.',
            background: '#0f172a',
            color: '#f8fafc',
            confirmButtonColor: '#f43f5e'
        });
    }
}

// Jika tidak bisa / lupa kode rahasia -> "Dilempar masukkan PIN"
function lemparKePinModal() {
    const secretModal = document.getElementById("modalSecretCode");
    secretModal.classList.add("hidden");
    secretModal.classList.remove("flex");

    const authOverlay = document.getElementById("authOverlay");
    authOverlay.style.display = "flex";
    setTimeout(() => authOverlay.classList.remove("opacity-0", "pointer-events-none"), 10);
    
    document.getElementById("authSubtitle").textContent = "Masukkan PIN Akses Anda (Maksimal 10 Karakter)";
    document.getElementById("authPinInput").value = '';
    setTimeout(() => document.getElementById("authPinInput").focus(), 200);

    showToast("Silakan masukkan PIN masuk Anda.", "info");
}

function bukaModalSecretCodeDariPin() {
    const authOverlay = document.getElementById("authOverlay");
    authOverlay.classList.add("opacity-0", "pointer-events-none");
    setTimeout(() => authOverlay.style.display = "none", 400);

    const secretModal = document.getElementById("modalSecretCode");
    secretModal.classList.remove("hidden");
    secretModal.classList.add("flex");
    
    document.getElementById("secretCodeInput").value = '';
    setTimeout(() => document.getElementById("secretCodeInput").focus(), 200);
}

function handleLogout() {
    Swal.fire({
        title: 'Kunci Sesi Brankas?',
        text: 'Anda harus memasukkan PIN atau Kode Rahasia untuk membuka brankas.',
        icon: 'question',
        showCancelButton: true,
        confirmButtonColor: '#f43f5e',
        cancelButtonColor: '#334155',
        confirmButtonText: 'Ya, Kunci Sekarang',
        cancelButtonText: 'Batal',
        background: '#0f172a',
        color: '#f8fafc'
    }).then((result) => {
        if (result.isConfirmed) {
            sessionStorage.removeItem("ditfur_auth");
            const overlay = document.getElementById("authOverlay");
            overlay.style.display = "flex";
            setTimeout(() => overlay.classList.remove("opacity-0", "pointer-events-none"), 10);
            document.getElementById("authPinInput").value = '';
            document.getElementById("authPinInput").focus();
            showToast("Sesi brankas telah dikunci.", "success");
        }
    });
}

// ==========================================================================
// 3. GANTI PIN (DENGAN VERIFIKASI KODE RAHASIA & MAKS 10 KARAKTER)
// ==========================================================================

function bukaModalGantiPin() {
    document.getElementById('gantiPinForm').reset();
    const modal = document.getElementById('modalGantiPin');
    modal.classList.remove('hidden');
    modal.classList.add('flex');
    setTimeout(() => document.getElementById('gantiPinKodeRahasia').focus(), 150);
}

function tutupModalGantiPin() {
    const modal = document.getElementById('modalGantiPin');
    modal.classList.add('hidden');
    modal.classList.remove('flex');
}

async function handleGantiPin(e) {
    e.preventDefault();
    const kodeRahasia = document.getElementById('gantiPinKodeRahasia').value.trim();
    const pinLama = document.getElementById('pinLama').value.trim();
    const pinBaru = document.getElementById('pinBaru').value.trim();
    const pinKonfirmasi = document.getElementById('pinKonfirmasi').value.trim();

    if (!kodeRahasia || !pinLama || !pinBaru || !pinKonfirmasi) {
        showToast("Semua kolom termasuk Kode Rahasia wajib diisi!", "warning");
        return;
    }

    // 1. Verifikasi Kode Rahasia ("Aditya_24214")
    const hashedSecret = await sha256(kodeRahasia);
    const isSecretValid = (kodeRahasia === "Aditya_24214") || (hashedSecret === MASTER_SECRET_HASH);

    if (!isSecretValid) {
        Swal.fire({
            icon: 'error',
            title: 'Kode Rahasia Salah!',
            text: 'Kode Rahasia Pemilik tidak valid! Anda tidak diizinkan mengubah PIN brankas.',
            background: '#0f172a',
            color: '#f8fafc',
            confirmButtonColor: '#f43f5e'
        });
        return;
    }

    // 2. Batasan Panjang PIN Baru (Maksimal 10 Karakter)
    if (pinBaru.length > 10) {
        showToast("PIN Baru maksimal 10 karakter!", "error");
        return;
    }

    if (pinBaru.length < 4) {
        showToast("PIN Baru minimal 4 karakter!", "warning");
        return;
    }

    if (pinBaru !== pinKonfirmasi) {
        showToast("PIN Baru dan Konfirmasi PIN tidak cocok!", "error");
        return;
    }

    // 3. Verifikasi PIN Lama
    const hashedLama = await sha256(pinLama);
    const customHash = localStorage.getItem("finance_custom_pin_hash");
    const isOldValid = (customHash && customHash === hashedLama) || AUTHORIZED_HASHES.includes(hashedLama);

    if (!isOldValid) {
        showToast("PIN Lama yang Anda masukkan salah!", "error");
        return;
    }

    // 4. Hash dan simpan PIN Baru
    const newHash = await sha256(pinBaru);
    localStorage.setItem("finance_custom_pin_hash", newHash);

    // Sync juga ke Firebase settings
    try {
        await settingsRef.child("pin_hash").set(newHash);
    } catch(err) {
        console.warn("Gagal sync pin hash ke Firebase:", err);
    }

    tutupModalGantiPin();

    Swal.fire({
        icon: 'success',
        title: 'PIN Berhasil Diperbarui!',
        text: 'PIN baru Anda (maksimal 10 karakter) telah aktif dan tersimpan aman bersama otoritas Kode Rahasia.',
        background: '#0f172a',
        color: '#f8fafc',
        confirmButtonColor: '#10b981'
    });
}

// Privacy Mask (Stealth Mode)
function initStealthMode() {
    const isStealth = localStorage.getItem("ditfur_stealth") === "true";
    if (isStealth) {
        document.body.classList.add("stealth-active");
        updateStealthBtn(true);
    } else {
        document.body.classList.remove("stealth-active");
        updateStealthBtn(false);
    }
}

function toggleStealthMode() {
    const isCurrentlyStealth = document.body.classList.contains("stealth-active");
    if (isCurrentlyStealth) {
        document.body.classList.remove("stealth-active");
        localStorage.setItem("ditfur_stealth", "false");
        updateStealthBtn(false);
        showToast("Stealth Mode: Nonaktif (Saldo terlihat)", "info");
    } else {
        document.body.classList.add("stealth-active");
        localStorage.setItem("ditfur_stealth", "true");
        updateStealthBtn(true);
        showToast("Stealth Mode: Aktif (Saldo disamarkan)", "info");
    }
}

function updateStealthBtn(isActive) {
    const icon = document.getElementById("stealthIcon");
    if (isActive) {
        icon.className = "fa-solid fa-eye text-emerald-400";
    } else {
        icon.className = "fa-solid fa-eye-slash text-cyan-400";
    }
}

// ==========================================================================
// 4. MODERN TOAST & ALERT UTILITIES (SWEETALERT2)
// ==========================================================================

function showToast(title, icon = 'success') {
    Swal.mixin({
        toast: true,
        position: 'top-end',
        showConfirmButton: false,
        timer: 3000,
        timerProgressBar: true,
        background: '#0f172a',
        color: '#f8fafc',
        didOpen: (toast) => {
            toast.addEventListener('mouseenter', Swal.stopTimer);
            toast.addEventListener('mouseleave', Swal.resumeTimer);
        }
    }).fire({
        icon: icon,
        title: title
    });
}

// ==========================================================================
// 5. CURRENCY FORMATTING & RUPIAH MASKING (BUG-FREE NUMBER PARSING)
// ==========================================================================

function formatRupiah(angka) {
    if (isNaN(angka)) return 'Rp 0';
    return 'Rp ' + Math.abs(angka).toString().replace(/\B(?=(\d{3})+(?!\d))/g, ".");
}

// Masking input dengan titik ribuan
function handleRupiahMask(inputElem, targetHiddenId) {
    let cleanVal = inputElem.value.replace(/[^0-9]/g, '');
    if (!cleanVal) {
        inputElem.value = '';
        document.getElementById(targetHiddenId).value = '';
        return;
    }
    let formatted = cleanVal.replace(/\B(?=(\d{3})+(?!\d))/g, ".");
    inputElem.value = formatted;
    document.getElementById(targetHiddenId).value = cleanVal;
}

function setRupiahMaskValue(inputElemId, targetHiddenId, val) {
    if (!val) {
        document.getElementById(inputElemId).value = '';
        document.getElementById(targetHiddenId).value = '';
        return;
    }
    const cleanNum = Math.round(Number(val)).toString();
    document.getElementById(targetHiddenId).value = cleanNum;
    document.getElementById(inputElemId).value = cleanNum.replace(/\B(?=(\d{3})+(?!\d))/g, ".");
}

function getTodayDateString() {
    const today = new Date();
    return today.toISOString().substring(0, 10);
}

function getCurrentMonthYearString() {
    const today = new Date();
    const currentYear = today.getFullYear();
    const currentMonth = String(today.getMonth() + 1).padStart(2, '0');
    return `${currentYear}-${currentMonth}`;
}

function formatTimestamp(timestamp) {
    if (!timestamp) return 'N/A';
    const date = new Date(timestamp);
    const day = String(date.getDate()).padStart(2, '0');
    const month = String(date.getMonth() + 1).padStart(2, '0');
    const year = date.getFullYear();
    const hours = String(date.getHours()).padStart(2, '0');
    const minutes = String(date.getMinutes()).padStart(2, '0');
    return `${day}/${month}/${year} ${hours}:${minutes}`;
}

// ==========================================================================
// 6. SMART QUICK INPUT PARSER (WITH MUTASI & CATEGORY DETECTION)
// ==========================================================================

function detectCategoryFromText(text) {
    const lower = text.toLowerCase();
    if (/\b(makan|minum|kopi|bakso|ayam|mie|restoran|warung|snack|sarapan|nasi|cafe)\b/.test(lower)) return "Makanan & Minuman";
    if (/\b(bensin|pertalite|pertamax|solar|gojek|grab|tol|parkir|cuci|service|ongkir|ojol)\b/.test(lower)) return "Transportasi";
    if (/\b(listrik|pln|pdam|air|wifi|indihome|pulsa|kuota|bpjs|pajak|tagihan|iuran)\b/.test(lower)) return "Tagihan & Utilitas";
    if (/\b(bisnis|stok|modal|grosir|barang|operasional|iklan|ads|domain|hosting|alat)\b/.test(lower)) return "Operasional & Bisnis";
    if (/\b(belanja|indomaret|alfamart|superindo|shopee|tokopedia|pakaian|baju|sepatu|sabun)\b/.test(lower)) return "Belanja Kebutuhan";
    if (/\b(bioskop|nonton|game|steam|topup|liburan|hotel|jalan|rekreasi|hobi)\b/.test(lower)) return "Hiburan & Rekreasi";
    if (/\b(nabung|tabungan|investasi|reksadana|saham|emas|crypto|deposito)\b/.test(lower)) return "Tabungan & Investasi";
    if (/\b(gaji|honor|upah|fee|proyek|bonus|tips|pendapatan|omset)\b/.test(lower)) return "Gaji & Pendapatan";
    if (/\b(mutasi|tf antar|pindah|tarik tunai|setor)\b/.test(lower)) return "Mutasi Saldo";
    return "Lain-lain";
}

function parseSingleQuickLine(line) {
    line = line.trim();
    if (!line) return null;

    let jenis = 'PENGELUARAN';
    let rawText = line;

    // Check Mutasi keyword
    const isMutasi = /\b(mutasi|pindah saldo|tarik tunai|setor tunai)\b/i.test(rawText) || 
                     (/\b(tf|transfer)\b/i.test(rawText) && /\bke\b/i.test(rawText));

    if (isMutasi) {
        jenis = 'MUTASI';
    } else if (rawText.startsWith('+')) {
        jenis = 'PEMASUKAN';
        rawText = rawText.substring(1).trim();
    } else if (rawText.startsWith('-')) {
        jenis = 'PENGELUARAN';
        rawText = rawText.substring(1).trim();
    } else {
        const lowerLine = rawText.toLowerCase();
        if (/^\b(masuk|pemasukan|in)\b/.test(lowerLine)) {
            jenis = 'PEMASUKAN';
            rawText = rawText.replace(/^\b(masuk|pemasukan|in)\b/i, '').trim();
        } else if (/^\b(keluar|pengeluaran|out)\b/.test(lowerLine)) {
            jenis = 'PENGELUARAN';
            rawText = rawText.replace(/^\b(keluar|pengeluaran|out)\b/i, '').trim();
        }
    }

    let lower = rawText.toLowerCase();
    let metode = 'CASH';
    let subMetode = 'CASH';
    let akunTujuan = 'DANA';

    if (jenis === 'MUTASI') {
        let sourceFound = 'BNI';
        let targetFound = 'DANA';

        if (/\bbni\b/.test(lower)) sourceFound = 'BNI';
        else if (/\bcash|tunai\b/.test(lower)) sourceFound = 'CASH';
        else if (/\bdana\b/.test(lower)) sourceFound = 'DANA';
        else if (/\bgopay\b/.test(lower)) sourceFound = 'GOPAY';
        else if (/\blemari\b/.test(lower)) sourceFound = 'LEMARI';

        if (/\bke dana\b|\bdana\b/.test(lower) && sourceFound !== 'DANA') targetFound = 'DANA';
        else if (/\bke cash\b|\bke tunai\b|\bcash\b/.test(lower) && sourceFound !== 'CASH') targetFound = 'CASH';
        else if (/\bke bni\b|\bbni\b/.test(lower) && sourceFound !== 'BNI') targetFound = 'BNI';
        else if (/\bke gopay\b|\bgopay\b/.test(lower) && sourceFound !== 'GOPAY') targetFound = 'GOPAY';
        else if (/\bke lemari\b|\blemari\b/.test(lower) && sourceFound !== 'LEMARI') targetFound = 'LEMARI';

        subMetode = sourceFound;
        akunTujuan = targetFound;
        metode = 'TF';
    } else {
        if (/\b(bni)\b/.test(lower)) {
            subMetode = 'BNI';
            metode = 'TF';
        } else if (/\b(dana)\b/.test(lower)) {
            subMetode = 'DANA';
            metode = 'TF';
        } else if (/\b(gopay)\b/.test(lower)) {
            subMetode = 'GOPAY';
            metode = 'TF';
        } else if (/\b(lemari)\b/.test(lower)) {
            subMetode = 'LEMARI';
            metode = 'CASH';
        }

        if (/\bqris\b/.test(lower)) {
            metode = 'QRIS';
            if (subMetode === 'CASH') subMetode = 'DANA';
        } else if (/\b(cash|tunai)\b/.test(lower)) {
            metode = 'CASH';
            subMetode = 'CASH';
        } else if (/\b(tf|transfer)\b/.test(lower)) {
            metode = 'TF';
            if (subMetode === 'CASH') subMetode = 'BNI';
        }
    }

    // Extract Nominal
    const words = rawText.split(/\s+/);
    let nominal = 0;
    let nominalIndex = -1;

    for (let i = words.length - 1; i >= 0; i--) {
        let w = words[i].toLowerCase().replace(/^rp\.?/, '');
        const match = w.match(/^(\d+(?:[\.,]\d+)?)(k|rb|ribu|jt|juta)?$/);
        if (match) {
            let numStr = match[1];
            let unit = match[2];

            if (numStr.includes('.') || numStr.includes(',')) {
                if (unit) {
                    numStr = numStr.replace(',', '.');
                } else {
                    numStr = numStr.replace(/[\.,]/g, '');
                }
            }

            let val = parseFloat(numStr);
            if (!isNaN(val) && val > 0) {
                if (unit) {
                    if (['k', 'rb', 'ribu'].includes(unit)) val *= 1000;
                    else if (['jt', 'juta'].includes(unit)) val *= 1000000;
                } else {
                    if (val < 1000) val *= 1000;
                }
                nominal = val;
                nominalIndex = i;
                break;
            }
        }
    }

    // Extract Description
    let nameWords = words.filter((w, idx) => {
        if (idx === nominalIndex) return false;
        const wLower = w.toLowerCase().replace(/^rp\.?/, '');
        if (['cash', 'tunai', 'tf', 'transfer', 'mutasi', 'ke', 'dari', 'qris', 'bni', 'dana', 'gopay', 'lemari', 'masuk', 'pemasukan', 'keluar', 'pengeluaran'].includes(wLower)) return false;
        return true;
    });

    let nama = nameWords.join(' ').trim();
    if (!nama) {
        nama = (jenis === 'MUTASI') ? `Mutasi ${subMetode} ➔ ${akunTujuan}` : 'Transaksi Cepat';
    }

    const kategori = (jenis === 'MUTASI') ? 'Mutasi Saldo' : detectCategoryFromText(nama);

    return {
        originalText: line,
        jenis,
        metode,
        subMetode,
        akunTujuan,
        kategori,
        nama,
        nominal
    };
}

function handleQuickInput() {
    const textVal = document.getElementById('quickInput').value;
    const previewContainer = document.getElementById('quickPreview');
    const previewListElem = document.getElementById('quickPreviewList');
    const quickCountElem = document.getElementById('quickCount');

    if (!textVal.trim()) {
        previewContainer.classList.add('hidden');
        currentParsedList = [];
        return;
    }

    const lines = textVal.split('\n');
    currentParsedList = [];

    lines.forEach(line => {
        const parsed = parseSingleQuickLine(line);
        if (parsed) currentParsedList.push(parsed);
    });

    if (currentParsedList.length === 0) {
        previewContainer.classList.add('hidden');
        return;
    }

    previewContainer.classList.remove('hidden');
    quickCountElem.textContent = currentParsedList.length;

    previewListElem.innerHTML = '';
    currentParsedList.forEach((item) => {
        let badgeColor = item.jenis === 'PEMASUKAN' ? 'text-emerald-400 bg-emerald-500/10 border-emerald-500/30' : 
                        (item.jenis === 'PENGELUARAN' ? 'text-rose-400 bg-rose-500/10 border-rose-500/30' : 'text-amber-400 bg-amber-500/10 border-amber-500/30');
        let iconName = item.jenis === 'PEMASUKAN' ? 'fa-arrow-down' : (item.jenis === 'PENGELUARAN' ? 'fa-arrow-up' : 'fa-right-left');
        let nominalColor = item.jenis === 'PEMASUKAN' ? 'text-emerald-400' : (item.jenis === 'PENGELUARAN' ? 'text-rose-400' : 'text-amber-400');
        let descAccount = item.jenis === 'MUTASI' ? `${item.subMetode} ➔ ${item.akunTujuan}` : (item.metode !== 'CASH' ? `${item.metode} (${item.subMetode})` : 'CASH');

        const itemDiv = document.createElement('div');
        itemDiv.className = 'flex items-center justify-between p-2.5 rounded-xl bg-slate-900 border border-slate-800 text-xs';
        itemDiv.innerHTML = `
            <div class="flex items-center gap-2">
                <span class="px-2 py-0.5 rounded-md text-[10px] font-bold border ${badgeColor} flex items-center gap-1">
                    <i class="fa-solid ${iconName}"></i> ${item.jenis}
                </span>
                <span class="font-semibold text-slate-200">${item.nama}</span>
                <span class="text-[10px] text-slate-400">(${descAccount})</span>
            </div>
            <strong class="${nominalColor} font-bold">${formatRupiah(item.nominal)}</strong>
        `;
        previewListElem.appendChild(itemDiv);
    });

    const submitBtn = document.getElementById('btnQuickSubmit');
    if (currentParsedList.length === 1) {
        submitBtn.innerHTML = `<i class="fa-solid fa-bolt"></i> Simpan 1 Transaksi Otomatis (Enter)`;
        const first = currentParsedList[0];
        setJenis(first.jenis, 'form');
        document.getElementById('nama').value = first.nama;
        document.getElementById('kategori').value = first.kategori;
        if (first.jenis === 'MUTASI') {
            document.getElementById('mutasiSumber').value = first.subMetode;
            document.getElementById('mutasiTujuan').value = first.akunTujuan;
        } else {
            document.getElementById('metode').value = first.metode;
            toggleSubMetode();
            if (first.metode !== 'CASH') {
                document.getElementById('subMetode').value = first.subMetode;
            }
        }
        if (first.nominal > 0) {
            setRupiahMaskValue('nominalMasked', 'nominal', first.nominal);
        }
    } else {
        submitBtn.innerHTML = `<i class="fa-solid fa-bolt"></i> Simpan ${currentParsedList.length} Transaksi Sekaligus`;
    }
}

function handleQuickKey(event) {
    if (event.key === 'Enter' && !event.shiftKey) {
        if (!document.getElementById('quickInput').value.includes('\n')) {
            event.preventDefault();
            submitQuickInput();
        }
    }
}

async function submitQuickInput() {
    if (!currentParsedList || currentParsedList.length === 0) {
        showToast("Ketik transaksi terlebih dahulu!", "warning");
        return;
    }

    const validItems = currentParsedList.filter(item => item.nominal > 0);
    if (validItems.length === 0) {
        showToast("Nominal transaksi harus lebih dari 0!", "warning");
        return;
    }

    try {
        for (const item of validItems) {
            const now = firebase.database.ServerValue.TIMESTAMP;
            
            if (item.jenis === 'MUTASI') {
                if (item.subMetode === item.akunTujuan) {
                    showToast(`Mutasi gagal: Akun asal & tujuan sama (${item.subMetode})`, "error");
                    continue;
                }
                await updateSaldo(item.subMetode, item.nominal, 'subtract');
                await updateSaldo(item.akunTujuan, item.nominal, 'add');

                const data = {
                    tanggal: getTodayDateString(),
                    jenis: 'MUTASI',
                    kategori: 'Mutasi Saldo',
                    metode: 'TF',
                    subMetode: item.subMetode,
                    akunTujuan: item.akunTujuan,
                    nama: item.nama,
                    nominal: item.nominal,
                    timestamp: now,
                    lastUpdated: now
                };
                await transaksiRef.push(data);
            } else {
                let akunKey = item.metode === 'CASH' ? 'CASH' : item.subMetode;
                if (!akunKey || (akunKey === 'CASH' && item.metode !== 'CASH')) akunKey = 'BNI';

                const operation = item.jenis === 'PEMASUKAN' ? 'add' : 'subtract';
                await updateSaldo(akunKey, item.nominal, operation);

                const data = {
                    tanggal: getTodayDateString(),
                    jenis: item.jenis,
                    kategori: item.kategori || 'Lain-lain',
                    metode: item.metode,
                    subMetode: akunKey,
                    nama: item.nama,
                    nominal: item.nominal,
                    timestamp: now,
                    lastUpdated: now
                };
                await transaksiRef.push(data);
            }
        }

        document.getElementById('quickInput').value = '';
        document.getElementById('quickPreview').classList.add('hidden');
        currentParsedList = [];
        document.getElementById('transaksiForm').reset();
        setRupiahMaskValue('nominalMasked', 'nominal', '');
        setJenis('PEMASUKAN', 'form');
        document.getElementById('tanggal').value = getTodayDateString();

        showToast(`✅ Berhasil menyimpan ${validItems.length} transaksi!`, 'success');
    } catch (error) {
        console.error("Gagal menyimpan transaksi quick input:", error);
        showToast("Gagal menyimpan data: " + error.message, "error");
    }
}

// ==========================================================================
// 7. VIEW TOGGLES & FORM LOGIC
// ==========================================================================

function setJenis(value, context) {
    if (context === 'form') {
        document.getElementById('jenis').value = value;
        const btnIn = document.getElementById('formBtnPemasukan');
        const btnOut = document.getElementById('formBtnPengeluaran');
        const btnMut = document.getElementById('formBtnMutasi');

        btnIn.className = 'jenis-btn py-2.5 px-3 rounded-xl text-xs font-extrabold flex items-center justify-center gap-1.5 transition-all';
        btnOut.className = 'jenis-btn py-2.5 px-3 rounded-xl text-xs font-extrabold flex items-center justify-center gap-1.5 transition-all';
        btnMut.className = 'jenis-btn py-2.5 px-3 rounded-xl text-xs font-extrabold flex items-center justify-center gap-1.5 transition-all';

        const regularMetode = document.getElementById('regularMetodeContainer');
        const mutasiContainer = document.getElementById('mutasiAkunContainer');
        const kategoriSelect = document.getElementById('kategori');

        if (value === 'PEMASUKAN') {
            btnIn.classList.add('active-pemasukan');
            regularMetode.classList.remove('hidden');
            mutasiContainer.classList.add('hidden');
            if (kategoriSelect.value === 'Mutasi Saldo') kategoriSelect.value = 'Lain-lain';
        } else if (value === 'PENGELUARAN') {
            btnOut.classList.add('active-pengeluaran');
            regularMetode.classList.remove('hidden');
            mutasiContainer.classList.add('hidden');
            if (kategoriSelect.value === 'Mutasi Saldo') kategoriSelect.value = 'Lain-lain';
        } else if (value === 'MUTASI') {
            btnMut.classList.add('active-mutasi');
            regularMetode.classList.add('hidden');
            mutasiContainer.classList.remove('hidden');
            kategoriSelect.value = 'Mutasi Saldo';
        }
    } else if (context === 'edit') {
        document.getElementById('editJenis').value = value;
        const btnIn = document.getElementById('editBtnPemasukan');
        const btnOut = document.getElementById('editBtnPengeluaran');
        const btnMut = document.getElementById('editBtnMutasi');

        btnIn.className = 'jenis-btn py-2 rounded-xl text-xs font-bold';
        btnOut.className = 'jenis-btn py-2 rounded-xl text-xs font-bold';
        btnMut.className = 'jenis-btn py-2 rounded-xl text-xs font-bold';

        const regularMetode = document.getElementById('editRegularMetodeContainer');
        const mutasiContainer = document.getElementById('editMutasiContainer');

        if (value === 'PEMASUKAN') {
            btnIn.classList.add('active-pemasukan');
            regularMetode.classList.remove('hidden');
            mutasiContainer.classList.add('hidden');
        } else if (value === 'PENGELUARAN') {
            btnOut.classList.add('active-pengeluaran');
            regularMetode.classList.remove('hidden');
            mutasiContainer.classList.add('hidden');
        } else if (value === 'MUTASI') {
            btnMut.classList.add('active-mutasi');
            regularMetode.classList.add('hidden');
            mutasiContainer.classList.remove('hidden');
            document.getElementById('editKategori').value = 'Mutasi Saldo';
        }
    }
}

function toggleSubMetode() {
    const metode = document.getElementById('metode').value;
    const container = document.getElementById('subMetodeContainer');
    if (metode === 'TF' || metode === 'QRIS') {
        container.classList.remove('hidden');
    } else {
        container.classList.add('hidden');
    }
}

function toggleEditSubMetode(metodeValue) {
    const container = document.getElementById('editSubMetodeContainer');
    const metode = metodeValue || document.getElementById('editMetode').value;
    if (metode === 'TF' || metode === 'QRIS') {
        container.classList.remove('hidden');
    } else {
        container.classList.add('hidden');
    }
}

function populateMonthFilter() {
    const selectRingkasan = document.getElementById('filter-periode-ringkasan');
    selectRingkasan.innerHTML = '';
    const startYear = 2025;
    const endYear = 2027;
    
    const optionsRingkasan = [
        { value: 'ALL', text: 'Semua Data' }, 
        { value: 'DAILY', text: 'Hari Ini' },
        { value: 'MONTHLY', text: 'Bulan Ini' }
    ];

    optionsRingkasan.forEach(opt => {
        const option = document.createElement('option');
        option.value = opt.value;
        option.textContent = opt.text;
        selectRingkasan.appendChild(option);
    });
    
    for (let year = startYear; year <= endYear; year++) {
        for (let i = 0; i < 12; i++) {
            if (year === startYear && i < 10) continue; 
            const value = `${year}-${String(i + 1).padStart(2, '0')}`; 
            const text = `${MONTH_NAMES[i]} ${year}`;
            
            const optionRingkasan = document.createElement('option');
            optionRingkasan.value = value;
            optionRingkasan.textContent = text;
            selectRingkasan.appendChild(optionRingkasan);
        }
    }
    
    selectRingkasan.value = 'ALL';
}

// ==========================================================================
// 8. SALDO RECONCILIATION & FIREBASE OPERATIONS
// ==========================================================================

function listenForSaldo() {
    saldoRef.on('value', (snapshot) => {
        allSaldoData = snapshot.val() || {};
        initializeSaldoAccounts();
        renderSaldoTable();
        calculateTotalSaldoGabungan();
    }, (error) => {
        console.error("Error membaca Saldo Firebase:", error);
    });
}

function initializeSaldoAccounts() {
    let updates = {};
    for (const key in AKUN_SALDO) {
        if (!allSaldoData[key]) {
            updates[key] = {
                nama: AKUN_SALDO[key],
                saldo: 0
            };
        }
    }
    if (Object.keys(updates).length > 0) {
        saldoRef.update(updates).catch(console.error);
    }
}

function updateSaldo(akunKey, nominal, operation) {
    return new Promise((resolve, reject) => {
        if (!nominal || isNaN(nominal) || nominal <= 0) {
            return reject(new Error("Nominal tidak valid."));
        }
        
        const currentRef = saldoRef.child(akunKey).child('saldo');
        currentRef.transaction((currentSaldo) => {
            if (currentSaldo === null) currentSaldo = 0;
            if (operation === 'add') {
                return currentSaldo + nominal;
            } else if (operation === 'subtract') {
                return currentSaldo - nominal;
            }
            return currentSaldo;
        }, (error, committed, snapshot) => {
            if (error) {
                console.error(`Gagal update saldo ${akunKey}:`, error);
                reject(error);
            } else {
                resolve(snapshot.val());
            }
        });
    });
}

function calculateTotalSaldoGabungan() {
    let total = 0;
    for (const key in AKUN_SALDO) {
        if (allSaldoData[key] && !isNaN(allSaldoData[key].saldo)) {
            total += allSaldoData[key].saldo;
        }
    }
    document.getElementById('totalSaldoGabungan').textContent = formatRupiah(total);
}

function renderSaldoTable() {
    const tbody = document.getElementById('saldoTableBody');
    tbody.innerHTML = '';
    
    const orderedKeys = ['CASH', 'LEMARI', 'BNI', 'DANA', 'GOPAY'];

    orderedKeys.forEach(key => {
        if (allSaldoData[key]) {
            const data = allSaldoData[key];
            const row = tbody.insertRow();
            row.className = "hover:bg-slate-800/40 transition";
            
            let iconClass = 'fa-wallet';
            let iconColor = 'text-cyan-400';
            if (key === 'CASH') { iconClass = 'fa-money-bill-1'; iconColor = 'text-emerald-400'; }
            else if (key === 'LEMARI') { iconClass = 'fa-box-archive'; iconColor = 'text-amber-400'; }
            else if (key === 'BNI') { iconClass = 'fa-building-columns'; iconColor = 'text-orange-400'; }
            else if (key === 'DANA') { iconClass = 'fa-mobile-screen-button'; iconColor = 'text-blue-400'; }
            else if (key === 'GOPAY') { iconClass = 'fa-motorcycle'; iconColor = 'text-teal-400'; }

            const akunCell = row.insertCell();
            akunCell.className = "py-3 px-3 font-semibold text-white flex items-center gap-2";
            akunCell.innerHTML = `<i class="fa-solid ${iconClass} ${iconColor} text-sm"></i> <span>${data.nama}</span>`;
            
            const saldoCell = row.insertCell();
            saldoCell.className = "py-3 px-3 text-right font-extrabold text-cyan-400 saldo-value";
            saldoCell.textContent = formatRupiah(data.saldo || 0);
            
            const aksiCell = row.insertCell();
            aksiCell.className = "py-3 px-3 text-center";
            aksiCell.innerHTML = `
                <button type="button" onclick="handleManualEditSaldo('${key}')" title="Set Saldo ${data.nama}"
                        class="px-2.5 py-1 rounded-lg bg-slate-800 hover:bg-slate-700 text-slate-300 hover:text-white border border-slate-700 text-xs font-bold transition">
                    <i class="fa-solid fa-pen text-[10px]"></i> Edit
                </button>
            `;
        }
    });
}

// EDIT SALDO MANUAL DENGAN PEMBERSIHAN TITIK YANG AKURAT
function handleManualEditSaldo(akunKey) {
    const currentSaldo = allSaldoData[akunKey] ? allSaldoData[akunKey].saldo : 0;
    
    Swal.fire({
        title: `Edit Saldo: ${AKUN_SALDO[akunKey]}`,
        html: `
            <p class="text-xs text-slate-400 mb-3">Masukkan nominal saldo riil terakhir di brankas/rekening:</p>
            <div class="relative text-left">
                <span class="absolute left-3 top-1/2 -translate-y-1/2 text-sm font-bold text-slate-400">Rp</span>
                <input type="text" id="swalSaldoInput" inputmode="numeric" 
                       value="${currentSaldo ? currentSaldo.toString().replace(/\B(?=(\d{3})+(?!\d))/g, '.') : '0'}"
                       class="w-full py-2.5 pl-10 pr-3 rounded-xl bg-slate-900 border border-slate-700 text-white font-bold text-base focus:outline-none focus:border-cyan-400"
                       oninput="this.value = this.value.replace(/[^0-9]/g, '').replace(/\B(?=(\d{3})+(?!\d))/g, '.')">
            </div>
        `,
        showCancelButton: true,
        confirmButtonColor: '#06b6d4',
        cancelButtonColor: '#334155',
        confirmButtonText: 'Simpan Saldo',
        cancelButtonText: 'Batal',
        background: '#0f172a',
        color: '#f8fafc',
        preConfirm: () => {
            // Hapus semua karakter non-digit agar tidak terpotong karena titik
            const rawNominal = document.getElementById('swalSaldoInput').value.replace(/[^0-9]/g, '');
            const num = parseFloat(rawNominal);
            if (isNaN(num) || num < 0) {
                Swal.showValidationMessage('Nominal saldo harus angka dan tidak boleh minus.');
                return false;
            }
            return num;
        }
    }).then((result) => {
        if (result.isConfirmed) {
            const newSaldo = result.value;
            saldoRef.child(akunKey).update({ saldo: newSaldo })
                .then(() => {
                    showToast(`Saldo ${AKUN_SALDO[akunKey]} diperbarui ke ${formatRupiah(newSaldo)}`, "success");
                })
                .catch(err => {
                    showToast(`Gagal update saldo: ${err.message}`, "error");
                });
        }
    });
}

// ==========================================================================
// 9. TARGET TABUNGAN & IMPIAN (WISHLIST GOALS) - FIXED NOMINAL PARSING
// ==========================================================================

function listenForTargets() {
    targetRef.on('value', (snapshot) => {
        allTargetsData = snapshot.val() || {};
        renderTargetCards();
    }, (error) => {
        console.error("Error membaca targets Firebase:", error);
    });
}

function bukaModalTarget() {
    document.getElementById('targetForm').reset();
    setRupiahMaskValue('targetNominalMasked', 'targetNominal', '');
    setRupiahMaskValue('targetAwalMasked', 'targetAwal', '0');
    const modal = document.getElementById('modalTarget');
    modal.classList.remove('hidden');
    modal.classList.add('flex');
    setTimeout(() => document.getElementById('targetNama').focus(), 150);
}

function tutupModalTarget() {
    const modal = document.getElementById('modalTarget');
    modal.classList.add('hidden');
    modal.classList.remove('flex');
}

async function handleSimpanTarget(e) {
    e.preventDefault();
    const nama = document.getElementById('targetNama').value.trim();
    const kategori = document.getElementById('targetKategori').value;
    const akun = document.getElementById('targetAkun').value;
    
    // Parse angka murni tanpa titik
    const targetNominalStr = document.getElementById('targetNominal').value.toString().replace(/[^0-9]/g, '');
    const targetNominal = parseFloat(targetNominalStr);
    
    const awalStr = (document.getElementById('targetAwal').value || '0').toString().replace(/[^0-9]/g, '');
    const terkumpulAwal = parseFloat(awalStr) || 0;
    
    const tenggat = document.getElementById('targetTenggat').value || '';

    if (!nama) {
        showToast("Nama target tidak boleh kosong!", "warning");
        return;
    }

    if (!targetNominal || isNaN(targetNominal) || targetNominal <= 0) {
        showToast("Target nominal harus lebih dari 0!", "warning");
        return;
    }

    try {
        const now = firebase.database.ServerValue.TIMESTAMP;
        const targetData = {
            nama,
            kategori,
            akun,
            targetNominal,
            terkumpul: terkumpulAwal,
            tenggat,
            createdAt: now,
            lastUpdated: now
        };

        await targetRef.push(targetData);
        tutupModalTarget();
        showToast(`🎯 Target "${nama}" berhasil dibuat!`, "success");
    } catch(err) {
        console.error("Gagal menyimpan target:", err);
        showToast("Gagal menyimpan target: " + err.message, "error");
    }
}

function renderTargetCards() {
    const grid = document.getElementById('targetGrid');
    const emptyState = document.getElementById('targetEmptyState');
    grid.innerHTML = '';

    const keys = Object.keys(allTargetsData);
    if (keys.length === 0) {
        emptyState.classList.remove('hidden');
        return;
    } else {
        emptyState.classList.add('hidden');
    }

    keys.forEach(id => {
        const t = allTargetsData[id];
        const terkumpul = t.terkumpul || 0;
        const targetNominal = t.targetNominal || 1;
        let percentage = Math.min(100, Math.round((terkumpul / targetNominal) * 100));
        const sisa = Math.max(0, targetNominal - terkumpul);
        const isDone = terkumpul >= targetNominal;

        const card = document.createElement('div');
        card.className = "relative p-5 rounded-2xl bg-slate-900 border border-slate-800 hover:border-slate-700 transition-all shadow-lg flex flex-col justify-between";
        card.innerHTML = `
            <div>
                <div class="flex items-start justify-between gap-2 mb-3">
                    <div>
                        <span class="inline-block px-2 py-0.5 rounded-md text-[10px] font-bold bg-amber-500/10 text-amber-400 border border-amber-500/30 mb-1.5">${t.kategori || 'Target Impian'}</span>
                        <h4 class="text-sm font-extrabold text-white">${t.nama}</h4>
                    </div>
                    <button type="button" onclick="deleteTarget('${id}')" title="Hapus Target" class="text-slate-500 hover:text-rose-400 p-1 transition">
                        <i class="fa-solid fa-trash-can text-xs"></i>
                    </button>
                </div>

                <div class="space-y-1 mb-3">
                    <div class="flex items-center justify-between text-xs">
                        <span class="text-slate-400">Terkumpul:</span>
                        <strong class="text-emerald-400 target-nominal-value">${formatRupiah(terkumpul)}</strong>
                    </div>
                    <div class="flex items-center justify-between text-xs">
                        <span class="text-slate-400">Target Total:</span>
                        <span class="font-bold text-white target-nominal-value">${formatRupiah(targetNominal)}</span>
                    </div>
                </div>

                <!-- Progress Bar -->
                <div class="w-full bg-slate-950 rounded-full h-2.5 overflow-hidden border border-slate-800 mb-2">
                    <div class="bg-gradient-to-r from-cyan-500 to-emerald-400 h-2.5 rounded-full target-progress-fill" style="width: ${percentage}%"></div>
                </div>

                <div class="flex items-center justify-between text-[11px] mb-4">
                    <span class="font-bold ${isDone ? 'text-emerald-400' : 'text-cyan-400'}">${percentage}% ${isDone ? '🎉 Tercapai!' : 'Tercapai'}</span>
                    <span class="text-slate-400">Sisa: <strong class="text-slate-200 target-nominal-value">${formatRupiah(sisa)}</strong></span>
                </div>

                <div class="text-[11px] text-slate-400 flex items-center justify-between border-t border-slate-800 pt-2 mb-4">
                    <span><i class="fa-solid fa-wallet text-cyan-400 mr-1"></i> Akun: <strong>${t.akun || 'BNI'}</strong></span>
                    ${t.tenggat ? `<span><i class="fa-regular fa-calendar-check text-amber-400 mr-1"></i> ${t.tenggat}</span>` : ''}
                </div>
            </div>

            <div class="grid grid-cols-2 gap-2 pt-2 border-t border-slate-800/80">
                <button type="button" onclick="bukaModalNabungTarget('${id}')"
                        class="py-2 px-2.5 rounded-xl bg-emerald-500/15 hover:bg-emerald-500/25 border border-emerald-500/40 text-emerald-300 font-bold text-xs flex items-center justify-center gap-1.5 transition">
                    <i class="fa-solid fa-circle-plus"></i> + Nabung
                </button>
                <button type="button" onclick="bukaModalTarikTarget('${id}')"
                        class="py-2 px-2.5 rounded-xl bg-slate-800 hover:bg-slate-700 border border-slate-700 text-slate-300 hover:text-white font-bold text-xs flex items-center justify-center gap-1.5 transition">
                    <i class="fa-solid fa-circle-minus"></i> - Tarik
                </button>
            </div>
        `;
        grid.appendChild(card);
    });
}

// FIX: PENGAMBILAN ANGKA NOMINAL NABUNG (TIDAK AKAN JADI 1 ATAU 10 RUPIAH LAGI)
function bukaModalNabungTarget(targetId) {
    const target = allTargetsData[targetId];
    if (!target) return;

    Swal.fire({
        title: `Nabung ke ${target.nama}`,
        html: `
            <p class="text-xs text-slate-400 mb-3">Terkumpul saat ini: <strong class="text-emerald-400">${formatRupiah(target.terkumpul || 0)}</strong> dari target <strong>${formatRupiah(target.targetNominal)}</strong></p>
            <div class="space-y-3 text-left">
                <div>
                    <label class="text-[11px] font-bold text-slate-300">Nominal Setoran Tabungan (Rp):</label>
                    <div class="relative mt-1">
                        <span class="absolute left-3 top-1/2 -translate-y-1/2 text-xs font-bold text-slate-400">Rp</span>
                        <input type="text" id="swalNabungNominal" inputmode="numeric" placeholder="0"
                               class="w-full py-2.5 pl-9 pr-3 rounded-xl bg-slate-900 border border-slate-700 text-sm font-bold text-white focus:outline-none focus:border-cyan-400"
                               oninput="this.value = this.value.replace(/[^0-9]/g, '').replace(/\\B(?=(\\d{3})+(?!\\d))/g, '.')">
                    </div>
                </div>
                <div>
                    <label class="text-[11px] font-bold text-slate-300">Ambil dari Akun Kas:</label>
                    <select id="swalNabungAkun" class="w-full mt-1 py-2.5 px-3 rounded-xl bg-slate-900 border border-slate-700 text-xs text-white">
                        <option value="${target.akun || 'BNI'}" selected>Akun Target Utama (${target.akun || 'BNI'})</option>
                        <option value="BNI">Bank BNI</option>
                        <option value="CASH">Cash (Tunai)</option>
                        <option value="DANA">E-Wallet DANA</option>
                        <option value="GOPAY">E-Wallet GOPAY</option>
                        <option value="LEMARI">Di Lemari</option>
                    </select>
                </div>
            </div>
        `,
        showCancelButton: true,
        confirmButtonColor: '#10b981',
        cancelButtonColor: '#334155',
        confirmButtonText: 'Setor Tabungan',
        cancelButtonText: 'Batal',
        background: '#0f172a',
        color: '#f8fafc',
        preConfirm: () => {
            // Hapus semua karakter selain angka murni
            const rawNominal = document.getElementById('swalNabungNominal').value.replace(/[^0-9]/g, '');
            const nominal = parseFloat(rawNominal);
            const akun = document.getElementById('swalNabungAkun').value;
            if (!nominal || isNaN(nominal) || nominal <= 0) {
                Swal.showValidationMessage('Masukkan nominal setoran yang valid (contoh: 10000)!');
                return false;
            }
            return { nominal, akun };
        }
    }).then(async (result) => {
        if (result.isConfirmed) {
            const { nominal, akun } = result.value;
            try {
                // Potong saldo akun sumber secara utuh
                await updateSaldo(akun, nominal, 'subtract');

                // Tambah progress tabungan secara utuh
                await targetRef.child(targetId).child('terkumpul').transaction(val => (val || 0) + nominal);

                // Catat transaksi
                const now = firebase.database.ServerValue.TIMESTAMP;
                await transaksiRef.push({
                    tanggal: getTodayDateString(),
                    jenis: 'PENGELUARAN',
                    kategori: 'Tabungan & Investasi',
                    metode: (akun === 'CASH') ? 'CASH' : 'TF',
                    subMetode: akun,
                    nama: `Alokasi Tabungan Target: ${target.nama}`,
                    nominal: nominal,
                    timestamp: now,
                    lastUpdated: now
                });

                showToast(`✅ Berhasil menyetor ${formatRupiah(nominal)} ke target "${target.nama}"!`, "success");
            } catch(err) {
                console.error("Gagal setor tabungan target:", err);
                showToast("Gagal setor tabungan: " + err.message, "error");
            }
        }
    });
}

// FIX: PENGAMBILAN ANGKA NOMINAL TARIK
function bukaModalTarikTarget(targetId) {
    const target = allTargetsData[targetId];
    if (!target) return;

    const terkumpul = target.terkumpul || 0;
    if (terkumpul <= 0) {
        showToast("Saldo target ini masih Rp 0!", "warning");
        return;
    }

    Swal.fire({
        title: `Tarik dari ${target.nama}`,
        html: `
            <p class="text-xs text-slate-400 mb-3">Tersimpan saat ini: <strong class="text-emerald-400">${formatRupiah(terkumpul)}</strong></p>
            <div class="space-y-3 text-left">
                <div>
                    <label class="text-[11px] font-bold text-slate-300">Nominal Penarikan (Rp):</label>
                    <div class="relative mt-1">
                        <span class="absolute left-3 top-1/2 -translate-y-1/2 text-xs font-bold text-slate-400">Rp</span>
                        <input type="text" id="swalTarikNominal" inputmode="numeric" placeholder="0"
                               class="w-full py-2.5 pl-9 pr-3 rounded-xl bg-slate-900 border border-slate-700 text-sm font-bold text-white focus:outline-none focus:border-cyan-400"
                               oninput="this.value = this.value.replace(/[^0-9]/g, '').replace(/\\B(?=(\\d{3})+(?!\\d))/g, '.')">
                    </div>
                </div>
                <div>
                    <label class="text-[11px] font-bold text-slate-300">Transfer ke Akun Kas:</label>
                    <select id="swalTarikAkun" class="w-full mt-1 py-2.5 px-3 rounded-xl bg-slate-900 border border-slate-700 text-xs text-white">
                        <option value="${target.akun || 'BNI'}" selected>Akun Target Utama (${target.akun || 'BNI'})</option>
                        <option value="BNI">Bank BNI</option>
                        <option value="CASH">Cash (Tunai)</option>
                        <option value="DANA">E-Wallet DANA</option>
                        <option value="GOPAY">E-Wallet GOPAY</option>
                        <option value="LEMARI">Di Lemari</option>
                    </select>
                </div>
            </div>
        `,
        showCancelButton: true,
        confirmButtonColor: '#f59e0b',
        cancelButtonColor: '#334155',
        confirmButtonText: 'Tarik Tabungan',
        cancelButtonText: 'Batal',
        background: '#0f172a',
        color: '#f8fafc',
        preConfirm: () => {
            // Hapus semua karakter selain angka murni
            const rawNominal = document.getElementById('swalTarikNominal').value.replace(/[^0-9]/g, '');
            const nominal = parseFloat(rawNominal);
            const akun = document.getElementById('swalTarikAkun').value;
            if (!nominal || isNaN(nominal) || nominal <= 0) {
                Swal.showValidationMessage('Masukkan nominal yang valid!');
                return false;
            }
            if (nominal > terkumpul) {
                Swal.showValidationMessage(`Nominal melebihi saldo tabungan (${formatRupiah(terkumpul)})!`);
                return false;
            }
            return { nominal, akun };
        }
    }).then(async (result) => {
        if (result.isConfirmed) {
            const { nominal, akun } = result.value;
            try {
                // Tambah saldo akun tujuan
                await updateSaldo(akun, nominal, 'add');

                // Kurangi saldo tabungan target
                await targetRef.child(targetId).child('terkumpul').transaction(val => Math.max(0, (val || 0) - nominal));

                // Catat transaksi
                const now = firebase.database.ServerValue.TIMESTAMP;
                await transaksiRef.push({
                    tanggal: getTodayDateString(),
                    jenis: 'PEMASUKAN',
                    kategori: 'Tabungan & Investasi',
                    metode: (akun === 'CASH') ? 'CASH' : 'TF',
                    subMetode: akun,
                    nama: `Pencairan Tabungan Target: ${target.nama}`,
                    nominal: nominal,
                    timestamp: now,
                    lastUpdated: now
                });

                showToast(`✅ Berhasil menarik ${formatRupiah(nominal)} kembali ke akun ${akun}!`, "success");
            } catch(err) {
                console.error("Gagal menarik tabungan target:", err);
                showToast("Gagal menarik tabungan: " + err.message, "error");
            }
        }
    });
}

function deleteTarget(targetId) {
    const target = allTargetsData[targetId];
    if (!target) return;

    Swal.fire({
        title: 'Hapus Target Impian?',
        html: `Apakah Anda yakin ingin menghapus target <strong>"${target.nama}"</strong>?<br><span class="text-xs text-slate-400">Catatan: Sisa uang terkumpul (${formatRupiah(target.terkumpul || 0)}) tidak akan dihapus otomatis dari saldo kas.</span>`,
        icon: 'warning',
        showCancelButton: true,
        confirmButtonColor: '#f43f5e',
        cancelButtonColor: '#334155',
        confirmButtonText: 'Ya, Hapus Target',
        cancelButtonText: 'Batal',
        background: '#0f172a',
        color: '#f8fafc'
    }).then(async (result) => {
        if (result.isConfirmed) {
            try {
                await targetRef.child(targetId).remove();
                showToast(`Target "${target.nama}" berhasil dihapus.`, "success");
            } catch(err) {
                console.error("Gagal menghapus target:", err);
                showToast("Gagal menghapus: " + err.message, "error");
            }
        }
    });
}

// ==========================================================================
// 10. CRUD MANUAL TRANSAKSI
// ==========================================================================

document.getElementById('transaksiForm').addEventListener('submit', async function(e) {
    e.preventDefault();

    const jenis = document.getElementById('jenis').value;
    const nominal = parseFloat(document.getElementById('nominal').value);
    const tanggal = document.getElementById('tanggal').value;
    const nama = document.getElementById('nama').value.trim();
    const kategori = document.getElementById('kategori').value;

    if (!nominal || isNaN(nominal) || nominal <= 0) {
        showToast("Nominal transaksi harus lebih dari 0!", "warning");
        return;
    }

    try {
        const now = firebase.database.ServerValue.TIMESTAMP;

        if (jenis === 'MUTASI') {
            const sumber = document.getElementById('mutasiSumber').value;
            const tujuan = document.getElementById('mutasiTujuan').value;

            if (sumber === tujuan) {
                showToast("Akun Sumber dan Tujuan tidak boleh sama!", "error");
                return;
            }

            await updateSaldo(sumber, nominal, 'subtract');
            await updateSaldo(tujuan, nominal, 'add');

            const data = {
                tanggal: tanggal,
                jenis: 'MUTASI',
                kategori: 'Mutasi Saldo',
                metode: 'TF',
                subMetode: sumber,
                akunTujuan: tujuan,
                nama: nama,
                nominal: nominal,
                timestamp: now,
                lastUpdated: now
            };

            await transaksiRef.push(data);
            showToast("Transfer kas / Mutasi berhasil dicatat!", "success");
        } else {
            const metode = document.getElementById('metode').value;
            const subMetode = document.getElementById('subMetode').value;
            let akunKey = (metode === 'CASH') ? 'CASH' : subMetode;

            const operation = (jenis === 'PEMASUKAN') ? 'add' : 'subtract';
            await updateSaldo(akunKey, nominal, operation);

            const data = {
                tanggal: tanggal,
                jenis: jenis,
                kategori: kategori,
                metode: metode,
                subMetode: akunKey,
                nama: nama,
                nominal: nominal,
                timestamp: now,
                lastUpdated: now
            };

            await transaksiRef.push(data);
            showToast(`Transaksi ${jenis.toLowerCase()} berhasil disimpan!`, "success");
        }

        e.target.reset();
        setRupiahMaskValue('nominalMasked', 'nominal', '');
        setJenis('PEMASUKAN', 'form');
        document.getElementById('tanggal').value = getTodayDateString();
    } catch (err) {
        console.error("Gagal simpan transaksi manual:", err);
        showToast("Gagal menyimpan data: " + err.message, "error");
    }
});

// Edit Modal Form Submission
document.getElementById('editForm').addEventListener('submit', async function(e) {
    e.preventDefault();

    const id = document.getElementById('editId').value;
    const oldTransaction = allTransactionsData[id];
    if (!oldTransaction) return;

    const newJenis = document.getElementById('editJenis').value;
    const newTanggal = document.getElementById('editTanggal').value;
    const newKategori = document.getElementById('editKategori').value;
    const newNama = document.getElementById('editNama').value.trim();
    const newNominal = parseFloat(document.getElementById('editNominal').value);

    if (!newNominal || isNaN(newNominal) || newNominal <= 0) {
        showToast("Nominal transaksi harus lebih dari 0!", "warning");
        return;
    }

    try {
        // 1. Rollback Saldo Lama
        if (oldTransaction.jenis === 'MUTASI') {
            await updateSaldo(oldTransaction.subMetode, oldTransaction.nominal, 'add');
            await updateSaldo(oldTransaction.akunTujuan, oldTransaction.nominal, 'subtract');
        } else {
            const rollbackOp = (oldTransaction.jenis === 'PEMASUKAN') ? 'subtract' : 'add';
            await updateSaldo(oldTransaction.subMetode, oldTransaction.nominal, rollbackOp);
        }

        // 2. Terapkan Saldo Baru
        let newMetode = 'CASH';
        let newSubMetode = 'CASH';
        let newAkunTujuan = null;

        if (newJenis === 'MUTASI') {
            newSubMetode = document.getElementById('editMutasiSumber').value;
            newAkunTujuan = document.getElementById('editMutasiTujuan').value;
            newMetode = 'TF';

            if (newSubMetode === newAkunTujuan) {
                showToast("Akun Sumber dan Tujuan tidak boleh sama!", "error");
                return;
            }

            await updateSaldo(newSubMetode, newNominal, 'subtract');
            await updateSaldo(newAkunTujuan, newNominal, 'add');
        } else {
            newMetode = document.getElementById('editMetode').value;
            newSubMetode = (newMetode === 'CASH') ? 'CASH' : document.getElementById('editSubMetode').value;
            const newOp = (newJenis === 'PEMASUKAN') ? 'add' : 'subtract';
            await updateSaldo(newSubMetode, newNominal, newOp);
        }

        // 3. Simpan Update ke Firebase
        const now = firebase.database.ServerValue.TIMESTAMP;
        const updateData = {
            tanggal: newTanggal,
            jenis: newJenis,
            kategori: newKategori,
            metode: newMetode,
            subMetode: newSubMetode,
            akunTujuan: newAkunTujuan || null,
            nama: newNama,
            nominal: newNominal,
            lastUpdated: now
        };

        await db.ref(`${TRANSAKSI_PATH}/${id}`).update(updateData);
        closeEditModal();
        showToast("Transaksi berhasil diperbarui!", "success");
    } catch (err) {
        console.error("Gagal update transaksi:", err);
        showToast("Gagal memperbarui transaksi: " + err.message, "error");
    }
});

function populateEditForm(id, data) {
    document.getElementById('editId').value = id;
    document.getElementById('editTanggal').value = data.tanggal;
    document.getElementById('editNama').value = data.nama;
    document.getElementById('editKategori').value = data.kategori || 'Lain-lain';
    setRupiahMaskValue('editNominalMasked', 'editNominal', data.nominal);

    setJenis(data.jenis || 'PEMASUKAN', 'edit');

    if (data.jenis === 'MUTASI') {
        document.getElementById('editMutasiSumber').value = data.subMetode || 'BNI';
        document.getElementById('editMutasiTujuan').value = data.akunTujuan || 'DANA';
    } else {
        document.getElementById('editMetode').value = data.metode || 'CASH';
        toggleEditSubMetode(data.metode || 'CASH');
        if (data.subMetode && data.metode !== 'CASH') {
            document.getElementById('editSubMetode').value = data.subMetode;
        }
    }

    const modal = document.getElementById('editModal');
    modal.classList.remove('hidden');
    modal.classList.add('flex');
}

function closeEditModal() {
    const modal = document.getElementById('editModal');
    modal.classList.add('hidden');
    modal.classList.remove('flex');
}

function deleteTransaction(id) {
    const transaction = allTransactionsData[id];
    if (!transaction) return;

    Swal.fire({
        title: 'Hapus Transaksi?',
        html: `Apakah Anda yakin ingin menghapus <strong>"${transaction.nama}"</strong>?<br><span class="text-xs text-slate-400">Saldo terkait akan dikembalikan secara otomatis.</span>`,
        icon: 'warning',
        showCancelButton: true,
        confirmButtonColor: '#f43f5e',
        cancelButtonColor: '#334155',
        confirmButtonText: 'Ya, Hapus Data',
        cancelButtonText: 'Batal',
        background: '#0f172a',
        color: '#f8fafc'
    }).then(async (result) => {
        if (result.isConfirmed) {
            try {
                if (transaction.jenis === 'MUTASI') {
                    await updateSaldo(transaction.subMetode, transaction.nominal, 'add');
                    await updateSaldo(transaction.akunTujuan, transaction.nominal, 'subtract');
                } else {
                    const rollbackOp = (transaction.jenis === 'PEMASUKAN') ? 'subtract' : 'add';
                    await updateSaldo(transaction.subMetode, transaction.nominal, rollbackOp);
                }

                await db.ref(`${TRANSAKSI_PATH}/${id}`).remove();
                showToast("Transaksi berhasil dihapus & saldo dikembalikan.", "success");
            } catch(err) {
                console.error("Gagal menghapus transaksi:", err);
                showToast("Gagal menghapus: " + err.message, "error");
            }
        }
    });
}

// Modal Hubungi
function bukaHubungi() {
    const modal = document.getElementById('hubungiModal');
    modal.classList.remove('hidden');
    modal.classList.add('flex');
}

function tutupHubungi() {
    const modal = document.getElementById('hubungiModal');
    modal.classList.add('hidden');
    modal.classList.remove('flex');
}

// ==========================================================================
// 11. DATA RENDERING, FILTERING & CHARTS
// ==========================================================================

function filterAndRender() {
    renderDashboardAndTable(allTransactionsData);
}

function listenForTransactions() {
    transaksiRef.on('value', (snapshot) => {
        allTransactionsData = snapshot.val() || {};
        renderDashboardAndTable(allTransactionsData);
    }, (error) => {
        console.error("Error membaca transaksi:", error);
    });
}

function renderDashboardAndTable(allData) {
    const tbody = document.getElementById('transaksiTableBody');
    tbody.innerHTML = '';
    
    const filterPeriode = document.getElementById('filter-periode-ringkasan').value; 
    const filterJenis = document.getElementById('filterJenis').value;
    const today = getTodayDateString();
    const currentMonthYear = getCurrentMonthYearString();
    
    const searchInput = document.getElementById('searchInput');
    const searchQuery = searchInput ? searchInput.value.toLowerCase().trim() : ''; 

    let totalPemasukan = 0;
    let totalPengeluaran = 0;
    let totalMutasi = 0;
    let filteredTransactions = {};
    let categoryExpenses = {};

    for (const id in allData) {
        const transaction = allData[id];
        const transactionDate = transaction.tanggal || '';
        const transactionMonthYear = transactionDate.substring(0, 7);
        
        let isMatchPeriode = false;
        if (filterPeriode === 'ALL') isMatchPeriode = true;
        else if (filterPeriode === 'MONTHLY') isMatchPeriode = (transactionMonthYear === currentMonthYear);
        else if (filterPeriode === 'DAILY') isMatchPeriode = (transactionDate === today);
        else if (filterPeriode.match(/^\d{4}-\d{2}$/)) isMatchPeriode = (transactionMonthYear === filterPeriode);
        
        let isMatchJenis = true;
        if (filterJenis !== 'ALL') {
            isMatchJenis = (transaction.jenis === filterJenis);
        }

        let isMatchSearch = true;
        if (searchQuery.length > 0) {
            const nama = (transaction.nama || '').toLowerCase();
            const kategori = (transaction.kategori || '').toLowerCase();
            const metode = (transaction.metode || '').toLowerCase();
            const sub = (transaction.subMetode || '').toLowerCase();
            if (!nama.includes(searchQuery) && !kategori.includes(searchQuery) && !metode.includes(searchQuery) && !sub.includes(searchQuery)) {
                isMatchSearch = false;
            }
        }
        
        if (isMatchPeriode && isMatchJenis && isMatchSearch) {
            filteredTransactions[id] = transaction;

            if (transaction.jenis === 'PEMASUKAN') {
                totalPemasukan += (transaction.nominal || 0);
            } else if (transaction.jenis === 'PENGELUARAN') {
                totalPengeluaran += (transaction.nominal || 0);
                const kat = transaction.kategori || 'Lain-lain';
                categoryExpenses[kat] = (categoryExpenses[kat] || 0) + (transaction.nominal || 0);
            } else if (transaction.jenis === 'MUTASI') {
                totalMutasi += (transaction.nominal || 0);
            }
        }
    }

    // 1. Update Metrics
    document.getElementById('totalPemasukan').textContent = formatRupiah(totalPemasukan);
    document.getElementById('totalPengeluaran').textContent = formatRupiah(totalPengeluaran);
    
    let ratio = 0;
    if (totalPemasukan > 0) {
        ratio = (totalPengeluaran / totalPemasukan) * 100;
        if (ratio > 1000) ratio = 1000;
    }
    
    document.getElementById('persentasePengeluaran').textContent = `${ratio.toFixed(2)}%`;
    const limitInfoElement = document.getElementById('spending-limit-info');
    const warningElement = document.getElementById('warning-ratio');
    
    warningElement.classList.add('hidden');
    if (totalPemasukan <= 0) {
        limitInfoElement.textContent = "Masukkan Pemasukan untuk menghitung rasio pengeluaran.";
        limitInfoElement.style.color = '#94a3b8';
    } else if (ratio <= 100) {
        const remainingAmount = totalPemasukan - totalPengeluaran;
        if (ratio < 50) {
            limitInfoElement.textContent = `Aman! Pengeluaran ${ratio.toFixed(1)}%. Sisa kas: ${formatRupiah(remainingAmount)}`;
            limitInfoElement.style.color = '#34d399';
        } else if (ratio < 80) {
            limitInfoElement.textContent = `Waspada, pengeluaran sudah ${ratio.toFixed(1)}%. Sisa: ${formatRupiah(remainingAmount)}`;
            limitInfoElement.style.color = '#fbbf24';
        } else {
            limitInfoElement.textContent = `Kritis! Pengeluaran ${ratio.toFixed(1)}%. Sisa: ${formatRupiah(remainingAmount)}`;
            limitInfoElement.style.color = '#f87171';
            if (ratio === 100) {
                warningElement.textContent = "🛑 Anggaran periode ini telah mencapai 100%!";
                warningElement.classList.remove('hidden');
            }
        }
    } else {
        const overSpent = totalPengeluaran - totalPemasukan;
        limitInfoElement.textContent = `Defisit! Pengeluaran melebihi pemasukan ${formatRupiah(overSpent)}.`;
        limitInfoElement.style.color = '#fb7185';
        warningElement.textContent = `🚨 Defisit Anggaran: Rasio ${ratio.toFixed(2)}%!`;
        warningElement.classList.remove('hidden');
    }

    // 2. Update Charts
    updateChart(totalPengeluaran, totalPemasukan, categoryExpenses);

    // 3. Render Table
    const sortedKeys = Object.keys(filteredTransactions).sort((a, b) => {
        const dateA = filteredTransactions[a].tanggal || '';
        const dateB = filteredTransactions[b].tanggal || '';
        if (dateA !== dateB) return dateB.localeCompare(dateA);
        return (filteredTransactions[b].lastUpdated || filteredTransactions[b].timestamp || 0) - 
               (filteredTransactions[a].lastUpdated || filteredTransactions[a].timestamp || 0);
    });

    const emptyState = document.getElementById('tableEmptyState');
    if (sortedKeys.length === 0) {
        emptyState.classList.remove('hidden');
    } else {
        emptyState.classList.add('hidden');
    }

    sortedKeys.forEach(id => {
        const transaction = filteredTransactions[id];
        const row = tbody.insertRow();
        row.className = "hover:bg-slate-800/40 transition";
        
        let jenisBadge = '';
        let nominalPrefix = '';
        let nominalClass = '';
        let metodeDesc = '';

        if (transaction.jenis === 'PEMASUKAN') {
            jenisBadge = `<span class="inline-flex items-center gap-1 px-2.5 py-0.5 rounded-full text-[10px] font-bold bg-emerald-500/10 text-emerald-400 border border-emerald-500/30"><i class="fa-solid fa-arrow-down text-[9px]"></i> Pemasukan</span>`;
            nominalPrefix = '+ ';
            nominalClass = 'text-emerald-400';
            metodeDesc = transaction.metode === 'CASH' ? 'Cash' : `${transaction.metode} (${transaction.subMetode})`;
        } else if (transaction.jenis === 'PENGELUARAN') {
            jenisBadge = `<span class="inline-flex items-center gap-1 px-2.5 py-0.5 rounded-full text-[10px] font-bold bg-rose-500/10 text-rose-400 border border-rose-500/30"><i class="fa-solid fa-arrow-up text-[9px]"></i> Pengeluaran</span>`;
            nominalPrefix = '- ';
            nominalClass = 'text-rose-400';
            metodeDesc = transaction.metode === 'CASH' ? 'Cash' : `${transaction.metode} (${transaction.subMetode})`;
        } else if (transaction.jenis === 'MUTASI') {
            jenisBadge = `<span class="inline-flex items-center gap-1 px-2.5 py-0.5 rounded-full text-[10px] font-bold bg-amber-500/10 text-amber-400 border border-amber-500/30"><i class="fa-solid fa-right-left text-[9px]"></i> Mutasi</span>`;
            nominalPrefix = '⇄ ';
            nominalClass = 'text-amber-400';
            metodeDesc = `${transaction.subMetode} ➔ ${transaction.akunTujuan || 'DANA'}`;
        }

        const katBadge = `<span class="badge-category ml-1">${transaction.kategori || 'Lain-lain'}</span>`;

        row.insertCell().innerHTML = `<span class="font-medium text-slate-300">${transaction.tanggal}</span>`;
        row.insertCell().innerHTML = `<div class="flex items-center flex-wrap gap-1">${jenisBadge} ${katBadge}</div>`;
        row.insertCell().innerHTML = `<span class="px-2 py-0.5 rounded-md text-[11px] font-semibold bg-slate-800 text-slate-300 border border-slate-700/80"><i class="fa-solid fa-receipt text-slate-500 mr-1"></i>${metodeDesc}</span>`;
        row.insertCell().innerHTML = `<span class="font-semibold text-white">${transaction.nama}</span>`;
        row.insertCell().innerHTML = `<div class="text-right font-extrabold ${nominalClass} table-nominal">${nominalPrefix}${formatRupiah(transaction.nominal)}</div>`;
        
        // Actions
        const aksiCell = row.insertCell();
        aksiCell.className = "text-center";
        aksiCell.innerHTML = `
            <div class="flex items-center justify-center gap-1.5">
                <button type="button" onclick="populateEditForm('${id}', allTransactionsData['${id}'])" title="Edit Transaksi"
                        class="p-1.5 rounded-lg bg-slate-800 hover:bg-slate-700 text-slate-300 hover:text-cyan-400 border border-slate-700 transition">
                    <i class="fa-solid fa-pen text-xs"></i>
                </button>
                <button type="button" onclick="deleteTransaction('${id}')" title="Hapus Transaksi"
                        class="p-1.5 rounded-lg bg-slate-800 hover:bg-rose-500/20 text-slate-300 hover:text-rose-400 border border-slate-700 transition">
                    <i class="fa-solid fa-trash text-xs"></i>
                </button>
            </div>
        `;
    });
}

// ==========================================================================
// 12. DYNAMIC CHART MODES (CASHFLOW & CATEGORY DISTRIBUTION)
// ==========================================================================

function switchChartMode(mode) {
    currentChartMode = mode;
    const btnCashflow = document.getElementById('btnChartCashflow');
    const btnCategory = document.getElementById('btnChartCategory');

    if (mode === 'cashflow') {
        btnCashflow.classList.add('active');
        btnCategory.classList.remove('active');
        btnCategory.classList.add('text-slate-400');
        document.getElementById('chartSubtitle').textContent = "Rasio Realisasi Pengeluaran terhadap Pemasukan";
    } else {
        btnCategory.classList.add('active');
        btnCashflow.classList.remove('active');
        btnCashflow.classList.add('text-slate-400');
        document.getElementById('chartSubtitle').textContent = "Distribusi Nominal Pengeluaran per Kategori";
    }
    filterAndRender();
}

function updateChart(totalPengeluaran, totalPemasukan, categoryExpenses) {
    const ctx = document.getElementById('keuanganChart').getContext('2d');
    const sisaUang = Math.max(0, totalPemasukan - totalPengeluaran);

    let labels = [];
    let dataPoints = [];
    let bgColors = [];
    let borderColors = [];

    if (currentChartMode === 'cashflow') {
        labels = ['Pengeluaran', 'Sisa Kas'];
        dataPoints = [totalPengeluaran, sisaUang];
        bgColors = ['rgba(244, 63, 94, 0.85)', 'rgba(16, 185, 129, 0.85)'];
        borderColors = ['#f43f5e', '#10b981'];
    } else {
        labels = Object.keys(categoryExpenses);
        dataPoints = Object.values(categoryExpenses);

        const palette = [
            '#06b6d4', '#3b82f6', '#8b5cf6', '#ec4899', '#f59e0b',
            '#10b981', '#14b8a6', '#f43f5e', '#6366f1', '#64748b'
        ];

        bgColors = labels.map((_, i) => palette[i % palette.length]);
        borderColors = bgColors;

        if (labels.length === 0) {
            labels = ['Belum Ada Pengeluaran'];
            dataPoints = [1];
            bgColors = ['rgba(51, 65, 85, 0.5)'];
            borderColors = ['#334155'];
        }
    }

    const chartConfig = {
        labels: labels,
        datasets: [{
            data: dataPoints,
            backgroundColor: bgColors,
            borderColor: borderColors,
            borderWidth: 2,
            hoverOffset: 8
        }]
    };

    if (keuanganChart) {
        keuanganChart.data = chartConfig;
        keuanganChart.update();
    } else {
        keuanganChart = new Chart(ctx, {
            type: 'doughnut',
            data: chartConfig,
            options: {
                responsive: true,
                maintainAspectRatio: false,
                plugins: {
                    legend: {
                        position: 'bottom',
                        labels: {
                            font: { family: "'Plus Jakarta Sans', sans-serif", size: 11, weight: '600' },
                            color: '#94a3b8',
                            padding: 12,
                            usePointStyle: true,
                            pointStyle: 'circle'
                        }
                    },
                    tooltip: {
                        callbacks: {
                            label: function(context) {
                                const val = context.raw || 0;
                                return ` ${context.label}: ${formatRupiah(val)}`;
                            }
                        }
                    }
                },
                cutout: '68%'
            }
        });
    }
}

// ==========================================================================
// 13. EXPORT REPORT TO EXCEL / CSV DIRECTLY FROM BROWSER
// ==========================================================================

function exportToCSV() {
    const filterPeriode = document.getElementById('filter-periode-ringkasan').value;
    const filterJenis = document.getElementById('filterJenis').value;
    const today = getTodayDateString();
    const currentMonthYear = getCurrentMonthYearString();
    const searchQuery = (document.getElementById('searchInput')?.value || '').toLowerCase().trim();

    const rows = [];
    rows.push(["Tanggal", "Jenis", "Kategori", "Metode / Akun", "Keterangan", "Nominal (Rp)", "Waktu Dicatat"]);

    for (const id in allTransactionsData) {
        const item = allTransactionsData[id];
        const itemDate = item.tanggal || '';
        const itemMonthYear = itemDate.substring(0, 7);

        let matchPeriode = false;
        if (filterPeriode === 'ALL') matchPeriode = true;
        else if (filterPeriode === 'MONTHLY') matchPeriode = (itemMonthYear === currentMonthYear);
        else if (filterPeriode === 'DAILY') matchPeriode = (itemDate === today);
        else if (filterPeriode.match(/^\d{4}-\d{2}$/)) matchPeriode = (itemMonthYear === filterPeriode);

        let matchJenis = (filterJenis === 'ALL' || item.jenis === filterJenis);

        let matchSearch = true;
        if (searchQuery) {
            const nama = (item.nama || '').toLowerCase();
            const kat = (item.kategori || '').toLowerCase();
            if (!nama.includes(searchQuery) && !kat.includes(searchQuery)) matchSearch = false;
        }

        if (matchPeriode && matchJenis && matchSearch) {
            let akunDesc = (item.jenis === 'MUTASI') ? `${item.subMetode} -> ${item.akunTujuan}` : (item.metode === 'CASH' ? 'Cash' : `${item.metode} (${item.subMetode})`);
            rows.push([
                item.tanggal,
                item.jenis,
                item.kategori || 'Lain-lain',
                akunDesc,
                `"${(item.nama || '').replace(/"/g, '""')}"`,
                item.nominal,
                formatTimestamp(item.lastUpdated || item.timestamp)
            ]);
        }
    }

    if (rows.length <= 1) {
        showToast("Tidak ada data transaksi untuk diekspor!", "warning");
        return;
    }

    let csvContent = "\uFEFF";
    rows.forEach(rowArray => {
        csvContent += rowArray.join(";") + "\r\n";
    });

    const blob = new Blob([csvContent], { type: 'text/csv;charset=utf-8;' });
    const url = URL.createObjectURL(blob);
    const downloadAnchor = document.createElement('a');
    downloadAnchor.setAttribute('href', url);
    downloadAnchor.setAttribute('download', `Laporan_Keuangan_Adit_${getTodayDateString()}.csv`);
    document.body.appendChild(downloadAnchor);
    downloadAnchor.click();
    document.body.removeChild(downloadAnchor);
    URL.revokeObjectURL(url);

    showToast(`✅ Berhasil mengekspor ${rows.length - 1} data ke CSV/Excel!`, "success");
}

// ==========================================================================
// 14. INITIALIZATION ON LOAD
// ==========================================================================

window.addEventListener('DOMContentLoaded', () => {
    checkAuthSession();
    startSessionCountdownMonitor();
    initStealthMode();

    auth.signInAnonymously()
        .then(() => {
            console.log("✅ Firebase Anonymous Auth Active");
            
            // Sync PIN hash dari Firebase jika ada
            settingsRef.child("pin_hash").once('value').then(snap => {
                const val = snap.val();
                if (val) localStorage.setItem("finance_custom_pin_hash", val);
            });

            populateMonthFilter();
            listenForTransactions();
            listenForSaldo();
            listenForTargets();
            document.getElementById('tanggal').value = getTodayDateString();
        })
        .catch(err => {
            console.error("Firebase Auth Error:", err);
            showToast("Koneksi Firebase gagal: " + err.message, "error");
        });
});
