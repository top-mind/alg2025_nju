# filter dpdgraph output to keep only certain nodes and edges
def filter_lines(lines):
    A = set()

    for line in lines:
        line = line.strip()
        if line.startswith('N') and 'sign_eval' in line: # and 'prop=yes' in line and 'kind=cnst' in line:
            number = line.split('N: ')[1].split()[0]
            A.add(number)
            yield line
        elif line.startswith('E'):
            parts = line.split('E: ')[1].split()
            x, y = parts[0], parts[1]
            if x in A and y in A:
                yield line

if __name__ == "__main__":
    import sys
    for filtered_line in filter_lines(sys.stdin):
        print(filtered_line)