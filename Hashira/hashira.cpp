#include <iostream>
#include <vector>
#include <string>
#include <fstream>
#include <stdexcept>
#include <algorithm>

// --- Library Dependencies ---
// 1. A BigInt library. The code below assumes a header-only library "BigInt.h".
//    You can find one on GitHub, for example: https://github.com/mattmccutchen/bigint
#include "BigInt.h" 
// 2. The nlohmann/json library for JSON parsing.
#include "json.hpp"

using json = nlohmann::json;

// Converts a string value from a given base to BigInt
BigInt baseToDecimal(const std::string& value, int base) {
    BigInt res = 0;
    BigInt p = 1;
    for (int i = value.length() - 1; i >= 0; i--) {
        int digit;
        if (value[i] >= '0' && value[i] <= '9') {
            digit = value[i] - '0';
        } else if (value[i] >= 'a' && value[i] <= 'z') {
            digit = value[i] - 'a' + 10;
        } else if (value[i] >= 'A' && value[i] <= 'Z') {
            digit = value[i] - 'A' + 10;
        } else {
            throw std::invalid_argument("Invalid character in number string");
        }
        if (digit >= base) {
            throw std::invalid_argument("Digit out of range for the given base");
        }
        res += digit * p;
        p *= base;
    }
    return res;
}

// A large predefined prime to use for Shamir's Secret Sharing
// This is a 256-bit prime number which is more than enough for our needs
const BigInt LARGE_PRIME("115792089237316195423570985008687907853269984665640564039457584007913129639747");

// Forward declarations for functions used by other functions
BigInt modInverse(BigInt a, BigInt m);
List<BigInt> polyMulLimited(const std::vector<BigInt>& a, const std::vector<BigInt>& b, int limit, const BigInt& prime);

// Lagrange interpolation at x=0 to find the secret (optimized)
BigInt lagrangeInterpolation(const std::vector<std::vector<BigInt>>& points, const BigInt& prime) {
    BigInt secret = 0;
    int k = points.size();

    // Precompute the denominators for efficiency
    std::vector<BigInt> denoms(k, 1);
    for (int i = 0; i < k; ++i) {
        BigInt xi = points[i][0];
        for (int j = 0; j < k; ++j) {
            if (i != j) {
                denoms[i] = (denoms[i] * (xi - points[j][0])) % prime;
            }
        }
        denoms[i] = modInverse(denoms[i], prime);
    }

    // Compute the secret using the optimized approach
    for (int i = 0; i < k; ++i) {
        BigInt yi = points[i][1];
        BigInt lagrange = denoms[i];
        for (int j = 0; j < k; ++j) {
            if (i != j) {
                lagrange = (lagrange * (-points[j][0])) % prime;
            }
        }
        secret = (secret + (yi * lagrange)) % prime;
    }
    return (secret + prime) % prime;
}

// Extended Euclidean Algorithm for modular inverse (optimized)
BigInt modInverse(BigInt a, BigInt m) {
    if (m == 1) return 0;

    BigInt m0 = m;
    BigInt y = 0;
    BigInt x = 1;

    a %= m;
    if (a < 0) a += m;

    while (a > 1) {
        BigInt q = a / m;
        BigInt t = m;

        m = a % m;
        a = t;

        t = y;
        y = x - q * y;
        x = t;
    }

    if (x < 0) x += m0;
    return x;
}

// Reconstructs the full polynomial coefficients using Lagrange interpolation (optimized)
std::vector<BigInt> lagrangeCoefficients(const std::vector<std::vector<BigInt>>& points, const BigInt& prime) {
    int k = points.size();
    std::vector<BigInt> coeffs(k, 0);

    // Precompute denominators
    std::vector<BigInt> denoms(k, 1);
    for (int i = 0; i < k; ++i) {
        BigInt xi = points[i][0];
        for (int j = 0; j < k; ++j) {
            if (i != j) {
                denoms[i] = (denoms[i] * (xi - points[j][0])) % prime;
            }
        }
        denoms[i] = modInverse(denoms[i], prime);
    }

    for (int i = 0; i < k; ++i) {
        BigInt yi = points[i][1];

        // Compute the basis polynomial for this point
        std::vector<BigInt> basis(k, 0);
        basis[0] = 1;
        int deg = 0;

        for (int j = 0; j < k; ++j) {
            if (i != j) {
                BigInt xj = points[j][0];
                std::vector<BigInt> term = {-xj, 1};
                basis = polyMulLimited(basis, term, deg + 1, prime);
                deg++;
            }
        }

        // Scale by yi * inverse of denominator
        BigInt scale = (yi * denoms[i]) % prime;
        for (int d = 0; d <= deg; ++d) {
            basis[d] = (basis[d] * scale) % prime;
        }

        // Add to coefficients
        for (int d = 0; d <= deg; ++d) {
            coeffs[d] = (coeffs[d] + basis[d]) % prime;
        }
    }
    return coeffs;
}


// Optimized polynomial multiplication that only computes terms up to degree limit
std::vector<BigInt> polyMulLimited(const std::vector<BigInt>& a, const std::vector<BigInt>& b, int limit, const BigInt& prime) {
    std::vector<BigInt> res(limit + 1, 0);
    for (size_t i = 0; i < a.size() && i <= limit; ++i) {
        for (size_t j = 0; j < b.size() && i + j <= limit; ++j) {
            res[i + j] = (res[i + j] + a[i] * b[j]) % prime;
        }
    }
    return res;
}

// Evaluate polynomial at x (mod prime) - optimized with Horner's method
BigInt evalPoly(const std::vector<BigInt>& coeffs, const BigInt& x, const BigInt& prime) {
    BigInt result = 0;
    for (int i = coeffs.size() - 1; i >= 0; --i) {
        result = (result * x + coeffs[i]) % prime;
    }
    return result;
}

int main(int argc, char* argv[]) {
    if (argc < 2) {
        std::cerr << "Usage: " << argv[0] << " <input.json>" << std::endl;
        return 1;
    }

    std::ifstream file(argv[1]);
    if (!file.is_open()) {
        std::cerr << "Error: Could not open file " << argv[1] << std::endl;
        return 1;
    }

    json data;
    try {
        data = json::parse(file);
    } catch (json::parse_error& e) {
        std::cerr << "JSON parse error: " << e.what() << std::endl;
        return 1;
    }

    int k = data["keys"]["k"];

    // Collect all shares
    std::vector<std::vector<BigInt>> allPoints;
    for (auto& [key, val] : data.items()) {
        if (key == "keys") continue;
        int base = val["base"];
        BigInt value = baseToDecimal(val["value"], base);
        allPoints.push_back({BigInt(std::stoi(key)), value});
    }

    if (allPoints.size() < k) {
        std::cout << "Not enough shares to reconstruct the secret." << std::endl;
        return 0;
    }

    // Use the first k shares to reconstruct the secret
    std::vector<std::vector<BigInt>> points(allPoints.begin(), allPoints.begin() + k);

    // Use the predefined large prime
    BigInt prime = LARGE_PRIME;

    std::cout << "Reconstructing secret..." << std::endl;
    BigInt secret = lagrangeInterpolation(points, prime);
    std::cout << "Recovered secret: " << secret.toString() << std::endl;

    // Check for wrong shares
    std::cout << "Checking for wrong shares..." << std::endl;
    std::vector<std::vector<BigInt>> wrongShares;

    // Optimize by computing polynomial coefficients once
    std::vector<BigInt> coeffs = lagrangeCoefficients(points, prime);

    for (const auto& pt : allPoints) {
        BigInt x = pt[0];
        BigInt y = pt[1];
        BigInt fx = evalPoly(coeffs, x, prime);
        // Ensure fx is in the range [0, prime-1] for correct comparison
        BigInt normalized_fx = (fx + prime) % prime;
        if (normalized_fx != y) {
            wrongShares.push_back(pt);
        }
    }

    if (!wrongShares.empty()) {
        std::cout << "Wrong shares detected:" << std::endl;
        for (const auto& pt : wrongShares) {
            std::cout << "Share x=" << pt[0].toString() << ", value=" << pt[1].toString() << std::endl;
        }
    } else {
        std::cout << "No wrong shares detected." << std::endl;
    }

    return 0;
}