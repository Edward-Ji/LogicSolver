def print_table(table, aligns=None, widths=None, header=None):
    if widths is None:
        widths = [0] * max(map(len, table))
    if aligns is None:
        aligns = [""] * max(map(len, table))

    for args in [header] + table:
        for i, arg in enumerate(args):
            if len(arg) > widths[i]:
                widths[i] = len(arg)
    if header is not None:
        print(" | ", end="")
        for name, width in zip(header, widths):
            print(f"{name:^{width}s}", end=" | ")
        print()
        print(" | ", end="")
        for width in widths:
            print("-" * width, end=" | ")
        print()
    for args in table:
        print(" | ", end="")
        for arg, align, width in zip(args, aligns, widths):
            print(f"{arg:{align}{width}s}", end=" | ")
        print()


def latex_table(table, aligns=None, widths=None, header=None):
    if widths is None:
        widths = [0] * max(map(len, table))
    if aligns is None:
        aligns = [""] * max(map(len, table))

    align_map = dict(zip("<^>", "lcr"))
    align_str = ("|"
                 + "|".join(map(lambda k: align_map.get(k, "c"), aligns))
                 + "|")

    print(rf"\begin{{array}}{{{align_str}}}")
    if header is not None:
        print(" & ".join(header), r"\\")
        print(r"\hline")
    for args in table:
        print(" & ".join(args), r"\\")
    print(r"\end{array}")
