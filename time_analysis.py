import sys

try:
    from scipy import stats as scipy_stats
except ModuleNotFoundError:
    print("Need scipy for statistical analysis", file=sys.stderr)
    sys.exit(1)

if len(sys.argv) < 3:
    print("Need two filenames to compare", file=sys.stderr)
    sys.exit(1)

values = [[int(n) for n in open(file, "r").readlines()]
          for file in sys.argv[1:3]]

# Get the mean/variance
stats = list(map(scipy_stats.describe, values))
# Calculate both with and without the assumption of equal variance
p_eq_var = scipy_stats.ttest_ind(*values, equal_var=True).pvalue
p_uneq_var = scipy_stats.ttest_ind(*values, equal_var=False).pvalue

print("Mean")
for stat in stats:
    print(f"{stat.mean:.3f}")
print()
print("Standard deviation")
for stat in stats:
    print(f"{stat.variance**(1/2):.3f}")
print()
# Normal p-values are p<0.05 or even p<0.01 for statistical significance.
# Perhaps try a baseline where you compare the programs with themselves.
print("P values (small values -> reject equal mean hypothesis):")
print("Equal variance   Unequal variance")
print(f"{p_eq_var:.3f}            {p_uneq_var:.3f}")
