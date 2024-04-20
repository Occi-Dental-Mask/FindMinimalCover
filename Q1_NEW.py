import itertools


def remove_empty_lhs_rhs(fds):
    """
    Remove all the empty lhs or rhs case in the functional dependencies
    :param fds:
    :return:
    """
    res = []
    for fd_group in fds:
        left, right = fd_group
        if not left or not right:
            continue
        res.append(fd_group)
    return res


def find_subsets(s):
    """
    Given a set of attributes, return a list of all the proper subsets of the attributes
    input: {'A','B','C'}
    output: [{'A'}, {'A', 'B'}, {'A', 'C'}, {'B'}, {'B', 'C'}, {'C'}]
    :param s: a set of attributes
    :return: a list of sets, each set is a subset of the input set
    """
    s = list(s)
    subsets = []
    for r in range(1, len(s)):
        for subset in itertools.combinations(s, r):
            subsets.append(set(subset))
    return subsets




def fds_to_str_style(fds):
    """
    convert a set of functional dependencies to a list of strings
    :param fds: a list of functional dependencies
    :return: a list of strings
    """

    def fd_to_str(a):
        """
        to convert a functional dependency like [['A','B'], ['C']] to a string 'A,B->C'
        :param a:
        :return:
        """
        return ','.join(a[0]) + '->' + ','.join(a[1])

    ans = []
    for fd in fds:
        ans.append(fd_to_str(fd))
    return ans


def find_closure(attributes, dependencies):
    '''
    Given a series of attributes and dependencies, return the closure of the attributes
    :param attributes:
    :param dependencies:
    :return:
    '''
    closure = set(attributes)
    omega = []
    for item in dependencies:
        for right in item[1]:
            omega.append((set(item[0]), right))
    unused = omega[:]
    # [({'A'},'B'),({'A'},'C')]
    while len(unused) > 0:
        not_changed = True
        for i in range(len(unused)):
            if i >= len(unused):
                break
            dependency = unused[i]
            if dependency[0].issubset(closure):
                closure.add(dependency[1])
                not_changed = False
                unused.pop(i)
        if not_changed:
            break
    return closure


def remove_duplicates(lst):
    """
    remove duplicates in a list of lists
    :param lst:
    :return:
    """
    return [list(x) for x in set(tuple(sorted(x)) for x in lst)]


def handle_right_minimal_Q1(fds):
    """
    simplify the rhs of functional dependencies for Q1
    :return:
    """
    first_step_gen = []
    for fd in fds:
        left, right = fd.split('->')
        lhs_set = set(left.split(','))
        if len(right) > 1:
            for item in right.split(','):
                # if item not in lhs_set:
                first_step_gen.append(left + '->' + item)
        else:
            first_step_gen.append(fd)
    return first_step_gen


def simplify_lhs_Q1(fds):
    """
    simplify the lhs of the functional dependencies,
    if the subsets of the lhs implies the rhs, then replace the lhs by one of the valid subsets
    return all possible combinations of the replacements
    :param fds:
    :return:
    """

    def check_subset_closure(sub_sub, right, closure_memo):
        key = tuple(sorted(list(sub_sub)))
        closure = closure_memo[key] or find_closure_str_style(sub_sub, fds)
        closure_memo[key] = closure
        return right in closure

    closure_memo = dict()
    substitution = []

    for fd in fds:
        flag_replacement_fd = False
        left, right = fd.split('->')
        fd_lhs_subsets = find_subsets(left.split(','))
        for subset in fd_lhs_subsets:
            key = tuple(sorted(list(subset)))
            # indicates that the subset is possibly a replacement of the lhs of the fd
            closure_subset = closure_memo.get(key, None) or find_closure_str_style(subset, fds)
            closure_memo[key] = closure_subset
            if right in closure_memo[key]:
                if len(subset) > 1:
                    flag = True
                    # still need to check if the subset is a valid replacement
                    sub_sub_set = find_subsets(subset)
                    for sub_sub in sub_sub_set:
                        check_subset = check_subset_closure(sub_sub, right, closure_memo)
                        # for any subset of the subset SS is valid, then this subset SS is invalid
                        if check_subset:
                            flag = False
                            break
                    # print(subset, right)
                    # else the subset is valid and can be a replacement
                    if flag:
                        replacement_fd = ','.join(sorted(list(subset))) + '->' + right
                        substitution.append(replacement_fd)
                        flag_replacement_fd = True
                        break
                else:
                    # the subset only has one element, it is a valid replacement
                    replacement_fd = ','.join(sorted(list(subset))) + '->' + right
                    substitution.append(replacement_fd)
                    flag_replacement_fd = True
                    break
        if not flag_replacement_fd:
            substitution.append(fd)
    return substitution


def handle_whole_minimal_Q1(sec_step_gen):
    """
    handle the whole set simplification especially for Q1
    need to simplify the set itself by removing functional dependencies that can be derived
    :param sec_step_gen
    :return: the simplified set
    """

    def remove_redundant_fd(fds):
        """
        Remove all redundant fds
        check if rhs is still
        entailed in the absence of fd, if true then remove it
        :param fds:
        :return:
        """
        for fd in fds:
            fd_without_one = fds[:]
            fd_without_one.remove(fd)
            left, right = fd.split('->')
            if right in left:
                fds.remove(fd)
            elif right in find_closure_str_style(left, fd_without_one):
                fds.remove(fd)
        return fds

    return remove_redundant_fd(sec_step_gen)


def str_to_list_style_Q1(fds):
    """
    convert a list of strings to a list of lists
    :param fds:
    :return:
    """
    ans = []
    for fd in fds:
        left, right = fd.split('->')
        ans.append([left.split(','), [right]])
    return ans


def min_cover(fds):
    """
    find all the reachable minimal covers of fds
    :param fds:
    :return:
    """

    # remove all the empty lhs or rhs case in the functional dependencies
    fds = remove_empty_lhs_rhs(fds)
    # convert the fds to string style
    fds = fds_to_str_style(fds)
    # simplify the rhs of the fds
    fds = handle_right_minimal_Q1(fds)
    # simplify the lhs of the fds
    fds = simplify_lhs_Q1(fds)

    fds = handle_whole_minimal_Q1(fds)

    return str_to_list_style_Q1(fds)


fds =  [[['A', 'B', 'C'], ['B', 'D', 'E', 'A', 'C', 'G', 'H']], [['B'], ['D', 'E', 'B']], [['G'], ['B', 'D', 'E']]]

print(min_cover(fds))