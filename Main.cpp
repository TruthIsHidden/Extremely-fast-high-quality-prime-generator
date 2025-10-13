
#include <stdint.h>
#include <stdbool.h>
#include <vector>
#include <fstream>
#include <algorithm>
#include <unordered_set>
#include <iostream>
#include <string>
#include <bitset>
#include <random>
#include <iomanip>
#include <sstream>
#include <cctype>
#include <unordered_map>
#include <chrono>
#include <limits>
#include <cstdint>
#include <locale>
#include <map>
#include <set>

uint64_t ModPrime(uint64_t og, int irange, int erange);
uint64_t MidPrime(uint64_t og, int irange, int erange);
uint64_t MaxPrime(uint64_t og, int irange, int erange);
uint64_t TheoreticalMaxPrime(uint64_t og, int irange, int erange);
uint64_t PRNG(uint64_t value);
bool is_prime(uint64_t n);
using namespace std;

typedef uint64_t u64;
typedef unsigned __int128 u128; 

static inline u64 prng64_from(u64 &state) {
    state = PRNG(state);
    return state;
}

uint64_t rotate_left_64(uint64_t value, unsigned int positions) {
	positions %= 64;
	return (value << positions) | (value >> (64 - positions));
}

uint64_t rotate_right_64(uint64_t value, unsigned int positions) {
	positions %= 64;
	return (value >> positions) | (value << (64 - positions));
}

uint8_t rotate_left(uint8_t byte, unsigned int i) {
	i %= 8;
	return (byte << i) | (byte >> (8 - i));
}

uint8_t rotate_right(uint8_t byte, unsigned int i) {
	i %= 8;
	return (byte >> i) | (byte << (8 - i));
}

uint64_t PRNG(uint64_t value)
{
    uint64_t og = value;
    const uint64_t Tera = 5846788331219253894ULL;
    const uint64_t Tera_A = 14334443016395714402ULL;
    const uint64_t e = 57139ULL;
    const uint64_t pi_scaled = 314159ULL;
    const uint64_t GRC = 0x9E3779B97F4A7C15ULL;
    uint64_t salt = og ^ Tera;
    value ^= GRC;
    value ^= value >> 32;
    value ^= rotate_left_64(value, 31);
    value *= 0xD2B74407B1CE6E93ULL;
    value ^= rotate_left_64(value, 29);
    value = 2 * value + 13;

    for (int i = 0;i < 8;i++)
    {
        value ^= salt;
        uint8_t byte1 = (value >> 0) & 0xFF; //
        uint8_t byte2 = (value >> 8) & 0xFF;//
        uint8_t byte3 = (value >> 16) & 0xFF;//
        uint8_t byte4 = (value >> 24) & 0xFF;//
        uint8_t byte5 = (value >> 32) & 0xFF;//
        uint8_t byte6 = (value >> 40) & 0xFF;//
        uint8_t byte7 = (value >> 48) & 0xFF;//
        uint8_t byte8 = (value >> 56) & 0xFF;//
        byte1 *= (Tera + Tera_A) ^ (e + GRC);
        byte1 += ~i;
        byte1 ^= rotate_left(e + (uint8_t)pi_scaled ^ ~byte4, 3) ^ ~(byte7 << 3);
        byte8 ^= rotate_right(i ^ (uint8_t)Tera_A + byte1, 3) ^ (byte6 << 3);
        byte4 ^= rotate_left(~byte3 + byte6 ^ (uint8_t)Tera_A, 3) ^ (byte8 << 3) ^ (uint8_t)og;
        byte7 ^= rotate_right(byte7 - byte4 ^ (uint8_t)e, 3);
        byte5 ^= byte2;
        byte2 ^= rotate_right(Tera_A ^ i, 7);
        byte6 ^= (byte3 << 3) ^ byte5;
        byte3 ^= rotate_left(byte2 ^ ((uint8_t)og * ~byte2), 3);
        byte1 += byte8;
        byte2 += byte7;
        byte3 += byte6;
        byte4 += byte5;
        byte8 ^= byte7;
        byte7 ^= byte6;
        byte6 ^= byte5;
        byte5 ^= byte4;
        value = ((uint64_t)byte1 << 0)   // position 0
            | ((uint64_t)byte8 << 8)     // position 1
            | ((uint64_t)byte2 << 16)    // position 2
            | ((uint64_t)byte7 << 24)    // position 3
            | ((uint64_t)byte3 << 32)    // position 4
            | ((uint64_t)byte6 << 40)    // position 5
            | ((uint64_t)byte4 << 48)    // position 6
            | ((uint64_t)byte5 << 56);
        value ^= rotate_right_64(GRC ^ (uint64_t)i + (uint64_t)byte3 ^ (uint64_t)byte6 ^ ~(uint64_t)byte1, 33) * ~((uint64_t)byte4 ^ Tera);
        salt ^= rotate_left_64((uint64_t)byte5 ^ (uint64_t)byte3, 33) ^ (~value << 13) ^ ((19 - i) + ~i ^ byte6);
        value ^= og;
        value ^= value << 13;
    }
    return value;
}

u64 sample_k_wrapped(u64 K) {
    if (K == 0) return 0;

    // Band [L, H] = [floor(0.5*K), floor(1.5*K)]
    u128 L = (u128)K >> 1;                     // 0.5*K
    u128 H = (u128)K + (u128)(K >> 1);         // 1.5*K (safe in 128-bit)
    if (H < L) H = L;                          // (paranoia, should not happen)
    u128 span = H - L + 1;                     // span ∈ [1, 2^64]

    // Rejection sampling threshold to avoid modulo bias
    const u128 U = (u128)std::numeric_limits<u64>::max() + 1; // 2^64
    u128 t = (U / span) * span;                 // largest multiple of span below 2^64

    // Seed a local PRNG state from K (distinct from K itself to decorrelate)
    u64 state = PRNG(K ^ 0x9E3779B97F4A7C15ULL);

    u64 r;
    do {
        r = prng64_from(state);                 // get 64 random bits
    } while ((u128)r >= t);                     // reject high tail to keep uniformity

    // Map to the band, centered ("wrapped") around K
    u128 center = (u128)K - L;                  // 0 .. span-1
    u128 off    = (center + ((u128)r % span)) % span;
    return (u64)(L + off);
}


int counter = 0;
int tested_counter = 0;

uint64_t Poffset(uint64_t no, bool& found_prime)
{
    uint64_t use = no;
    uint64_t list[23] = { 1,5,11,13,17,19,23,25,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89 };
    vector<uint64_t> usable;
    int limit = 18;
    for (int i = 0; i < limit; i++)
    {
        if ((use + list[i]) % 7 != 0)
        {
            usable.push_back(list[i]);
            if (is_prime(use + list[i]))
            {
                cout << "Prime: " << (use + list[i]) << endl;
                found_prime = true;  
                return (use + list[i]);
            }
        }
          if (i == 17 && limit < 23) limit = 23;
    }
    cout << "Composite: " << (use + usable[0]) << endl;
    found_prime = false;  
    return use + usable[0];
}

// FIXED: Same fix for negative offset
uint64_t Noffset(uint64_t no, bool& found_prime)
{
    uint64_t use = no;
    uint64_t list[23] = { 1,5,11,13,17,19,23,25,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89 };
    vector<uint64_t> usable;
    int limit = 18;
    for (int i = 0; i < limit; i++)
    {
        if ((use - list[i]) % 7 != 0)
        {
            usable.push_back(list[i]);
            if (is_prime(use - list[i]))
            {
                cout << "Prime: " << (use - list[i]) << endl;
                found_prime = true; 
                return (use - list[i]);
            }
        }
          if (i == 17 && limit < 23) limit = 23;
    }
    cout << "Composite: " << (use - usable[0]) << endl;
    found_prime = false; 
    return use - usable[0];
}
/*bool is_prime(uint64_t n) {
    if (n < 2) return false;
    if (n == 2 || n == 3) return true;
    if (n % 2 == 0 || n % 3 == 0) return false;

    // Check divisibility by numbers of form 6k±1
    for (uint64_t i = 5; i * i <= n; i += 6) {
        if (n % i == 0 || n % (i + 2) == 0)
            return false;
    }
    return true;
}*/
uint64_t mod_mul(uint64_t a, uint64_t b, uint64_t mod) {
    uint64_t result = 0;
    a %= mod;
    while (b > 0) {
        if (b & 1) {
            result = (result + a) % mod;
        }
        a = (a * 2) % mod;
        b >>= 1;
    }
    return result;
}

// Modular exponentiation: (base^exp) % mod
uint64_t mod_pow(uint64_t base, uint64_t exp, uint64_t mod) {
    uint64_t result = 1;
    base %= mod;
    while (exp > 0) {
        if (exp & 1) {
            result = mod_mul(result, base, mod);
        }
        base = mod_mul(base, base, mod);
        exp >>= 1;
    }
    return result;
}

bool miller_rabin(uint64_t n, int rounds = 40) {
    if (n < 2) return false;
    if (n == 2 || n == 3) return true;
    if (n % 2 == 0) return false;

    uint64_t d = n - 1;
    int r = 0;
    while (d % 2 == 0) {
        d /= 2;
        r++;
    }

    uint64_t witnesses[] = { 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37 };
    int num_witnesses = (rounds < 12) ? rounds : 12;

    for (int i = 0; i < num_witnesses; i++) {
        uint64_t a = witnesses[i];
        if (a >= n) continue;

        uint64_t x = mod_pow(a, d, n);
        if (x == 1 || x == n - 1) continue;

        bool composite = true;
        for (int j = 0; j < r - 1; j++) {
            x = mod_mul(x, x, n);
            if (x == n - 1) {
                composite = false;
                break;
            }
        }
        if (composite) return false;
    }
    return true;
}

bool is_prime(uint64_t n) {
    return miller_rabin(n, 40);
}

uint64_t ModPrime(uint64_t og, uint64_t irange, uint64_t erange)
{
    int no = 0;
    int pos, neg;
    for (int i = irange;i < erange;i++)
    {
        pos = 6 * i + 13;
        neg = 6 * i - 13;
        if (is_prime(pos))
        {
            cout << "Prime: " << pos << endl;
            no++;
        }
        else cout << "Composite: " << pos << endl;
        if (is_prime(neg))
        {
            cout << "Prime: " << neg << endl;
            no++;
        }
        else cout << "Composite: " << neg << endl;
    }
    return no;
}
uint64_t MidPrime(uint64_t og, uint64_t irange, uint64_t erange)
{
    int no = 0;
    int pos, neg;
    for (int i = irange;i < erange;i++)
    {
        uint64_t main = 60 * i;
        pos = main + 1;
        neg = main - 1;
        if (is_prime(pos))
        {
            cout << "Prime: " << pos << endl;
            no++;
        }
        else cout << "Composite: " << pos << endl;
        if (is_prime(neg))
        {
            cout << "Prime: " << neg << endl;
            no++;
        }
        else cout << "Composite: " << neg << endl;
    }
    return no;
    return 0;

}
uint64_t TheoreticalMaxPrime(uint64_t og, uint64_t irange, uint64_t erange)
{
    int primes_found = 0;
    int total_attempts = 0;

    for (uint64_t i = irange; i < erange; i++)
    {
        uint64_t main = 30 * i;
        bool pos_is_prime = false;
        bool neg_is_prime = false;

        uint64_t pos = Poffset(main, pos_is_prime);
        uint64_t neg = Noffset(main, neg_is_prime);

        if (pos_is_prime) primes_found++;
        if (neg_is_prime) primes_found++;
        total_attempts += 2;
    }

    cout << "\nPrimes found: " << primes_found << "/" << total_attempts;
    if (total_attempts > 0) {
        cout << " (" << (double)(primes_found * 100) / (double)total_attempts << "%)" << endl;
    }

    return primes_found;
}

uint64_t TheoreticalMaxPrimeS(uint64_t og, uint64_t irange, uint64_t erange)
{
    int primes_found = 0;
    int total_attempts = 0;

    for (uint64_t i = irange; i < erange; i++)
    {
        u64 k = sample_k_wrapped(i);
        u128 base128 = (u128)30 * (u128)k;                   // do the multiply in 128-bit
        if (base128 > std::numeric_limits<u64>::max()) {     // guard: would overflow 64-bit
         continue; // or handle however you want
        }
        u64 main = (u64)base128;              
        bool pos_is_prime = false;
        bool neg_is_prime = false;

        uint64_t pos = Poffset(main, pos_is_prime);
        uint64_t neg = Noffset(main, neg_is_prime);

        if (pos_is_prime) primes_found++;
        if (neg_is_prime) primes_found++;
        total_attempts += 2;
    }
    cout << "\nPrimes found: " << primes_found << "/" << total_attempts;
    if (total_attempts > 0) {
        cout << " (" << (double)(primes_found * 100) / (double)total_attempts << "%)" << endl;
    }
    return (uint64_t)primes_found;
}
uint64_t MaxPrime(uint64_t og, uint64_t irange, uint64_t erange)
{
    int no = 0;
    int pos, neg;
    for (int i = irange;i < erange;i++)
    {
        uint64_t main = 42 * i;
        pos = ((main + 13) % 5 == 0) ? main + 11 : main + 13;
        neg = ((main - 13) % 5 == 0) ? main - 11 : main - 13;
        if (is_prime(pos))
        {
            cout << "Prime: " << pos << endl;
            no++;
        }
        else cout << "Composite: " << pos << endl;
        if (is_prime(neg))
        {
            cout << "Prime: " << neg << endl;
            no++;
        }
        else cout << "Composite: " << neg << endl;
    }
    return no;
}
int main() {
    int choice;
    uint64_t start, end;

    while (true) {
        cout << "\n=== PRIME GENERATOR ===" << endl;
        cout << "1. ModPrime (6k ± 13)" << endl;
        cout << "2. MidPrime (60k ± 1)" << endl;
        cout << "3. MaxPrime (42k ± {11,13})" << endl;
        cout << "4. TheoreticalMax (Dynamic 20-offset)" << endl;
        cout << "5. TheoreticalMax, ONEWAY-VARIANT" << endl;
        cout << "6. Exit" << endl;
        cout << "Choose method: ";
        cin >> choice;

        if (choice == 6) break;
        if (choice < 1 || choice > 5) {
            cout << "Invalid choice!" << endl;
            continue;
        }

        cout << "Enter start k: ";
        cin >> start;
        cout << "Enter end k: ";
        cin >> end;

        uint64_t primes_found, total_tested;

        switch (choice) {
        case 1:
            primes_found = ModPrime(0, start, end);
            total_tested = 2 * (end - start);
            cout << "Primes: " << primes_found << "/" << total_tested;
            cout << " (" << (primes_found * 100) / total_tested << "%)" << endl;
            break;

        case 2:
            primes_found = MidPrime(0, start, end);
            total_tested = 2 * (end - start);
            cout << "Primes: " << primes_found << "/" << total_tested;
            cout << " (" << (primes_found * 100) / total_tested << "%)" << endl;
            break;

        case 3:
            primes_found = MaxPrime(0, start, end);
            total_tested = 2 * (end - start);
            cout << "Primes: " << (double)primes_found << "/" << (double)total_tested;
            cout << " (" << (double)(primes_found * 100) / total_tested << "%)" << endl;
            break;

        case 4:
            counter = 0;
            tested_counter = 0;
            primes_found = TheoreticalMaxPrime(0, start, end);
            
            break;
        
        case 5:
        counter = 0;
        tested_counter = 0;
        primes_found = TheoreticalMaxPrimeS(0, start, end);
        break;
        }

        cout << "\nPress Enter to continue...";
        cin.ignore();
        cin.get();
    }

    return 0;
}
