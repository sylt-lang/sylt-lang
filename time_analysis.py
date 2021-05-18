import sys

if len(sys.argv) == 1:
    print(f"usage: {sys.argv[0]} [<file1> <file2> | '-']")
    print()
    print("Description:")
    print(" Compare the two sets of numbers given in <file1> and <file2>.")
    print(" If '-' is specified, input is read from stdin as ")
    print(" newline-delimited numbers with a '$' separating the two sets.")
    print(" The two sets should contain the same amount of numbers.")
    print()
    print("Output:")
    print(" Mean, standard deviation and the result from two hypothesis tests")
    print(" are printed to stdout. The null hypotheses of the two tests are")
    print(" that the two means are the same. The first test assumes equal")
    print(" variance, while the second does not.")
    sys.exit(0)

if sys.argv[1] == "-":
    # read two files delimited by '$' from stdin
    values = "".join(sys.stdin.readlines()).split("$\n")
    values = [[int(n) for n in lst.strip().split("\n")] for lst in values]
elif len(sys.argv) == 2:
    print("Either two files or '-' should be specified", file=sys.stderr)
    sys.exit(1)
else:
    # read the first two files passes as arguments
    values = [[int(n) for n in open(file, "r").readlines()]
              for file in sys.argv[1:3]]

try:
    from scipy import stats as scipy_stats
except ModuleNotFoundError:
    print("Need scipy for statistical analysis", file=sys.stderr)
    sys.exit(1)

# Get the mean/variance
stats = zip(sys.argv[1:3], list(map(scipy_stats.describe, values)))
# Calculate both p-values with and without the assumption of equal variance
p_eq_var = scipy_stats.ttest_ind(*values, equal_var=True).pvalue
p_uneq_var = scipy_stats.ttest_ind(*values, equal_var=False).pvalue

for (f, stat) in stats:
    print(f"{f:>10}: {stat.mean:15.3f}ms ± {stat.variance**(1/2):.3f}ms")
print()

# Normal p-values are p<0.05 or even p<0.01 for statistical significance.
# Perhaps try a baseline where you compare the programs with themselves.
print("P values (small values -> reject equal mean hypothesis):")
print("Equal variance   Unequal variance")
print(f"{p_eq_var:.3f}            {p_uneq_var:.3f}")
