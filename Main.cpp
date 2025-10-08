#include <stdint.h>
#include <stdbool.h>
#include <iostream>
#include <vector>

uint64_t ModPrime(uint64_t og, int irange, int erange);
uint64_t MidPrime(uint64_t og, int irange, int erange);
uint64_t MaxPrime(uint64_t og, int irange, int erange);
uint64_t TheoreticalMaxPrime(uint64_t og, int irange, int erange);
bool is_prime(uint64_t n);
using namespace std;

int counter = 0;
int tested_counter = 0;

uint64_t Poffset(const uint64_t& use, bool& found_prime)
{
    uint64_t list[18] = { 1,5,11,13,17,19,23,25,29,31,37,41,43,47,53,59,61,67 };
    vector<uint64_t> usable;

    for (const uint64_t& num : list)
    {
        if ((use + num) % 5 != 0)
        {
            usable.push_back(num);
            if (is_prime(use + num))
            {
                cout << "Prime: " << (use + num) << '\n';
                found_prime = true;
                return (use + num);
            }
        }
    }
    cout << "Composite: " << (use + usable[0]) << '\n';
    found_prime = false;
    return use + usable[0];
}

// FIXED: Same fix for negative offset
uint64_t Noffset(const uint64_t& use, bool& found_prime)
{
    uint64_t list[18] = { 1,5,11,13,17,19,23,25,29,31,37,41,43,47,53,59,61,67 };
    vector<uint64_t> usable;

    for (const uint64_t& num : list)
    {
        if ((use - num) % 5 != 0)
        {
            usable.push_back(num);
            if (is_prime(use - num))
            {
                cout << "Prime: " << (use - num) << '\n';
                found_prime = true;
                return (use - num);
            }
        }
    }

    cout << "Composite: " << (use - usable[0]) << '\n';
    found_prime = false;
    return use - usable[0];
}
bool is_prime(uint64_t n) {
    if (n < 2) return false;
    if (n == 2 || n == 3) return true;
    if (n % 2 == 0 || n % 3 == 0) return false;

    // Check divisibility by numbers of form 6k±1
    for (uint64_t i = 5; i * i <= n; i += 6) {
        if (n % i == 0 || n % (i + 2) == 0)
            return false;
    }
    return true;
}


uint64_t ModPrime(uint64_t og, const uint64_t& irange, const uint64_t& erange)
{
    uint64_t no = 0;
    uint64_t pos, neg;
    for (uint64_t i = irange; i < erange; ++i)
    {
        pos = 6 * i + 13;
        neg = 6 * i - 13;
        if (is_prime(pos))
        {
            cout << "Prime: " << pos << '\n';
            ++no;
        }
        else cout << "Composite: " << pos << '\n';
        if (is_prime(neg))
        {
            cout << "Prime: " << neg << '\n';
            ++no;
        }
        else cout << "Composite: " << neg << '\n';
    }
    return no;
}
uint64_t MidPrime(uint64_t og, const uint64_t& irange, const uint64_t& erange)
{
    uint64_t no = 0;
    uint64_t pos, neg;
    for (uint64_t i = irange; i < erange; ++i)
    {
        uint64_t main = 60 * i;
        pos = main + 1;
        neg = main - 1;
        if (is_prime(pos))
        {
            cout << "Prime: " << pos << '\n';
            ++no;
        }
        else cout << "Composite: " << pos << '\n';
        if (is_prime(neg))
        {
            cout << "Prime: " << neg << '\n';
            ++no;
        }
        else cout << "Composite: " << neg << '\n';
    }
    return no;

}
uint64_t TheoreticalMaxPrime(uint64_t og, const uint64_t& irange, const uint64_t& erange)
{
    int primes_found = 0;
    int total_attempts = 0;

    for (uint64_t i = irange; i < erange; ++i)
    {
        uint64_t main = 42 * i;
        bool pos_is_prime = false;
        bool neg_is_prime = false;

        uint64_t pos = Poffset(main, pos_is_prime);
        uint64_t neg = Noffset(main, neg_is_prime);

        if (pos_is_prime) ++primes_found;
        if (neg_is_prime) ++primes_found;
        total_attempts += 2;
    }

    cout << "\nPrimes found: " << primes_found << "/" << total_attempts;
    if (total_attempts > 0) {
        cout << " (" << (primes_found * 100) / total_attempts << "%)" << '\n';
    }

    return primes_found;
}
uint64_t MaxPrime(uint64_t og, const uint64_t& irange, const uint64_t& erange)
{
    uint64_t no = 0;
    uint64_t pos, neg;
    for (uint64_t i = irange; i < erange; ++i)
    {
        uint64_t main = 42 * i;
        pos = ((main + 13) % 5 == 0) ? main + 11 : main + 13;
        neg = ((main - 13) % 5 == 0) ? main - 11 : main - 13;
        if (is_prime(pos))
        {
            cout << "Prime: " << pos << '\n';
            ++no;
        }
        else cout << "Composite: " << pos << '\n';
        if (is_prime(neg))
        {
            cout << "Prime: " << neg << '\n';
            ++no;
        }
        else cout << "Composite: " << neg << '\n';
    }
    return no;
    return 0;
}
int main() {
    int choice;
    uint64_t start, end;

    while (true) {
        cout << "\n=== PRIME GENERATOR ===" << '\n';
        cout << "1. ModPrime (6k ± 13)" << '\n';
        cout << "2. MidPrime (60k ± 1)" << '\n';
        cout << "3. MaxPrime (42k ± {11,13})" << '\n';
        cout << "4. TheoreticalMax (Dynamic 20-offset)" << '\n';
        cout << "5. Exit" << '\n';
        cout << "Choose method: ";
        cin >> choice;

        if (choice == 5) break;
        if (choice < 1 || choice > 4) {
            cout << "Invalid choice!" << '\n';
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
            cout << " (" << (primes_found * 100) / total_tested << "%)" << '\n';
            break;

        case 2:
            primes_found = MidPrime(0, start, end);
            total_tested = 2 * (end - start);
            cout << "Primes: " << primes_found << "/" << total_tested;
            cout << " (" << (primes_found * 100) / total_tested << "%)" << '\n';
            break;

        case 3:
            primes_found = MaxPrime(0, start, end);
            total_tested = 2 * (end - start);
            cout << "Primes: " << primes_found << "/" << total_tested;
            cout << " (" << (primes_found * 100) / total_tested << "%)" << '\n';
            break;

        case 4:
            counter = 0;
            tested_counter = 0;
            primes_found = TheoreticalMaxPrime(0, start, end);
            break;

        default:
            break;
        }
        
        cout << "\nPress Enter to continue...";
        cin.ignore();
        cin.get();
    }
    
    return 0;
}
