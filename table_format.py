def print_table(table, aligns=None, widths=None):
    if widths is None:
        widths = [0] * max(map(len, table))
    if aligns is None:
        aligns = [""] * max(map(len, table))

    for args in table:
        for i, arg in enumerate(args):
            if len(arg) > widths[i]:
                widths[i] = len(arg)
    for args in table:
        print(" | ", end="")
        for arg, align, width in zip(args, aligns, widths):
            print(f"{arg:{align}{width}s}", end=" | ")
        print()
