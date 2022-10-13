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
