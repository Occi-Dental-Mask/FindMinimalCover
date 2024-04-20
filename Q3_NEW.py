import itertools


def remove_empty_lhs_rhs_Q3(fds):
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


def find_subsets_Q3(s):
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


def find_all_subsets_closure(fds, attributes, closure_cache):
    """
    find the closure of all the subsets of the attributes
    :param fds:
    :param attributes:
    :return:
    """
    subsets = find_subsets_Q3(attributes)
    for s in subsets:
        closure_cache[tuple(sorted(list(s)))] = find_closure(s, fds)
    return closure_cache


def handle_right_minimal_Q2(fds):
    """
    simplify the rhs of functional dependencies
    :return:
    """
    first_step_gen = []
    for fd in fds:
        left, right = fd.split('->')
        lhs_set = set(left.split(','))
        if len(right) > 1:
            for item in right.split(','):
                first_step_gen.append(left + '->' + item)
        else:
            first_step_gen.append(fd)
    return first_step_gen


def simplify_lhs(fds, closure_cache, lhs_replacement_cache):
    """
    simplify the lhs of the functional dependencies,
    if the subsets of the lhs implies the rhs, then replace the lhs by one of the valid subsets
    return all possible combinations of the replacements
    :param fds:
    :return:
    """

    def check_subset_closure(sub_sub, right):
        return right in closure_cache[tuple(sorted(list(sub_sub)))]

    def generate_combinations(index, current_combination):
        # Base case: if we've gone through all FDs, add the current combination to the result
        if index == len(fds):
            return [current_combination]

        # Get the current FD
        fd = fds[index]

        # If the FD can be replaced, generate combinations with each replacement
        if fd in lhs_replacement_cache:
            all_combinations = []
            for replacement in lhs_replacement_cache[fd]:
                with_replacement = generate_combinations(index + 1, current_combination + [replacement])
                all_combinations.extend(with_replacement)
            return all_combinations
        else:
            # If the FD can't be replaced, just add it to the current combination and continue
            return generate_combinations(index + 1, current_combination + [fd])

    for fd in fds:
        left, right = fd.split('->')
        fd_lhs_subsets = find_subsets_Q3(left.split(','))
        for subset in fd_lhs_subsets:
            # indicates that the subset is possibly a replacement of the lhs of the fd
            if right in closure_cache[tuple(sorted(list(subset)))]:
                if len(subset) > 1:
                    flag = True
                    # still need to check if the subset is a valid replacement
                    sub_sub_set = find_subsets_Q3(subset)
                    for sub_sub in sub_sub_set:
                        check_subset = check_subset_closure(sub_sub, right)
                        # for any subset of the subset SS is valid, then this subset SS is invalid
                        if check_subset:
                            flag = False
                            break
                    # print(subset, right)
                    # else the subset is valid and can be a replacement
                    if flag:
                        replacement_fd = ','.join(sorted(list(subset))) + '->' + right
                        lhs_replacement_cache[fd] = lhs_replacement_cache.get(fd, [])
                        lhs_replacement_cache[fd].append(replacement_fd)
                else:
                    # the subset only has one element, it is a valid replacement
                    replacement_fd = ','.join(sorted(list(subset))) + '->' + right
                    lhs_replacement_cache[fd] = lhs_replacement_cache.get(fd, [])
                    lhs_replacement_cache[fd].append(replacement_fd)

    return generate_combinations(0, [])


def handle_whole_minimal_Q2(sec_step_gen):
    """
    handle the whole set simplification especially for Q2
    need to simplify the set itself by removing functional dependencies that can be derived
    :param sec_step_gen
    :return: the simplified set
    """

    def find_closure_str_style(attributes, dependencies):
        """
        Given a series of attributes and dependencies, return the closure of the attributes
        :param attributes:
        :param dependencies:
        :return:
        """
        closure = set(attributes)
        omega = []
        # 'A,C->B'
        for item in dependencies:
            left, right = item.split('->')
            left_ls = left.split(',')
            omega.append((set(left_ls), right))
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

    def not_redundant(p):
        for i in range(len(p)):
            _left, _right = p[i].split('->')
            fd_without_one = p[:i] + p[i + 1:]
            if _right in find_closure_str_style(_left.split(','), fd_without_one):
                return False
        return True

    def dfs(fds, index, path, result):
        if index == len(fds) and not_redundant(path):
            result.append(path[:])
            return
        elif index == len(fds):
            return
        this_fd = fds[index]
        right = this_fd.split('->')[1]
        fds_without_this = fds[:index] + fds[index + 1:]
        attributes = this_fd.split('->')[0].split(',')
        closure = find_closure_str_style(attributes, fds_without_this)
        # if this fd can be entailed by others
        if right in closure:
            # Case 1: Remove the current FD and do recursion
            dfs(fds_without_this, index, path, result)
            # Case 2: Keep the current FD and do recursion (backtracking)
            dfs(fds, index + 1, path + [this_fd], result)
        else:
            # If the current FD cannot be entailed by other FDs, keep it and move to the next FD
            dfs(fds, index + 1, path + [this_fd], result)

    def find_all_combinations(fds):
        result = []
        dfs(fds, 0, [], result)
        return result

    return find_all_combinations(sec_step_gen)


def find_all_attributes(fds):
    attributes = set()
    for fd in fds:
        for attr_list in fd:
            for attr in attr_list:
                attributes.add(attr)
    return list(attributes)


def str_to_list_style(fdss):
    """
    convert a list of strings to a list of lists
    :param fds:
    :return:
    """
    ans = []
    for fds in fdss:
        fds_ls_style = []
        for fd in fds:
            left, right = fd.split('->')
            fds_ls_style.append([left.split(','), [right]])
        ans.append(fds_ls_style)
    return ans


def generate_all_reachable(fds, closure_cache):
    """
    Generate all the reachable functional dependencies
    :param fds:
    :return:
    """
    ans = []
    for fd in fds:
        left, right = fd
        closure = closure_cache[tuple(sorted(left))]
        for i in closure:
            if i != left[0]:
                ans.append([left, [i]])
    return ans


def all_minimal_covers(fds):
    # closure_cache is a dictionary that stores the closure of all the subsets of the attributes
    closure_cache = dict()
    # lhs_replacement_cache is a dictionary that stores the possible replacements of the lhs of the fds
    lhs_replacement_cache = dict()

    # find all the attributes
    attributes = find_all_attributes(fds)
    # remove all the empty lhs or rhs case in the functional dependencies
    fds = remove_empty_lhs_rhs_Q3(fds)
    # find the closure of all the subsets of the attributes(this step need to be executed first
    find_all_subsets_closure(fds, attributes, closure_cache)
    # Firstly generate all the reachable functional dependencies
    fds = generate_all_reachable(fds, closure_cache)
    # convert the fds to string style
    fds = fds_to_str_style(fds)
    # simplify the rhs of the fds
    fds = handle_right_minimal_Q2(fds)
    # simplify the lhs of the fds
    fds = simplify_lhs(fds, closure_cache, lhs_replacement_cache)

    final_result = []

    for sec_step_gen in fds:
        # simplify the whole set and add the simplified result to the whole result
        final_step_gen = handle_whole_minimal_Q2(sec_step_gen)
        for dependencies in final_step_gen:
            final_result.append(dependencies)
    # remove all the duplicates in the final result
    fdss = remove_duplicates(final_result)
    return str_to_list_style(fdss)

fds =  [[['A', 'B', 'C'], ['B', 'D', 'E', 'A', 'C', 'G', 'H']], [['B'], ['D', 'E', 'B']], [['G'], ['B', 'D', 'E']]]


print(all_minimal_covers(fds)   )