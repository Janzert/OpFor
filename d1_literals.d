/**
 * Floating point literals as DMD 1.076 read them.
 *
 * DMD 1's conversion of decimal literals to 80-bit reals wasn't always
 * correctly rounded (and depended on spelling: 0.1 and 0.10 differ). For
 * these literals in the evaluation its values are one bit off the correctly
 * rounded ones. Using the same values keeps evaluation, and so search
 * results, identical to the original D1 build. Hex floats are exact.
 */
module d1_literals;

enum real D1_0_00005 = 0xD1B71758E219652Dp-78L; // 0.00005
enum real D1_0_05 = 0xCCCCCCCCCCCCCCCCp-68L; // 0.05
enum real D1_0_09 = 0xB851EB851EB851EBp-67L; // 0.09
enum real D1_0_10 = 0xCCCCCCCCCCCCCCCCp-67L; // 0.10
enum real D1_0_15 = 0x9999999999999999p-66L; // 0.15
enum real D1_0_20 = 0xCCCCCCCCCCCCCCCCp-66L; // 0.20
enum real D1_0_33 = 0xA8F5C28F5C28F5C2p-65L; // 0.33
enum real D1_0_66 = 0xA8F5C28F5C28F5C2p-64L; // 0.66
enum real D1_0_85 = 0xD999999999999999p-64L; // 0.85
enum real D1_0_9 = 0xE666666666666667p-64L; // 0.9
enum real D1_0_92 = 0xEB851EB851EB851Ep-64L; // 0.92
enum real D1_0_98 = 0xFAE147AE147AE147p-64L; // 0.98
enum real D1_1_96 = 0xFAE147AE147AE147p-63L; // 1.96
enum real D1_9_4 = 0x9666666666666667p-60L; // 9.4
enum real D1_33_695652173913032 = 0x86C8590B21641F9Ap-58L; // 33.695652173913032
enum real D1_3369_562173913032 = 0xD298FEAA12B23048p-52L; // 3369.562173913032
