"""
Author: Noam Shveber
Program to calculate some of the functions used for the DB course in JCT.

Usage example is at end of file.
"""

from enum import Enum


class Action(Enum):
    EXIT = 0
    ALL_KEYS = 1
    CLOSURE = 2
    CHECK_LOSSLESS = 3
    CHECK_DEPENDENCIES_PRESERVING = 4
    MINIMAL_COVER = 5
    CALC_3NF = 6
    CALC_BCNF = 7
    CHECK_3NF = 8
    CHECK_BCNF = 9
    DEPENDENCIES_PROJECTION = 10
    CHECK_3NF_DECOMPOSITION = 11
    CHECK_BCNF_DECOMPOSITION = 12


def Minimize(X: str, F: str):
    """
    Minimizing a super-key to a key.
    :param X: The super-key
    :param F: String of rules
    :return: A minimized key created from X.
    """
    for a in X:
        if is_in(X, closure(F, X.replace(a, ''))):
            X = X.replace(a, '')

    return X


def FindKey(R: str, F: str):
    """
    Find a keys of a scheme and rule group.
    :param R: A scheme.
    :param F: String of rules
    :return: A key of R.
    """
    return Minimize(R, F)


def All_Keys(R: str, F: str) -> list:
    """
        Find all keys of a scheme and rule group.
        :param R: String of a scheme.
        :param F: String of rules
        :return: All key of R as a list.
        """
    k = FindKey(R, F)
    keyQueue = [k]
    keys = [k]
    while len(keyQueue) != 0:
        # Dequeue
        k = keyQueue[-1]
        keyQueue = keyQueue[:-1]

        for rule in F.split(','):
            spl = rule.split('->')
            if intersect(spl[1], k) != '':
                s = union(difference(k, spl[1]), spl[0])  # S is a super-key!
                if not any([(key in s) for key in keys]):
                    _s = Minimize(s, F)
                    keys += [_s]
                    keyQueue += [_s]

    return keys


def intersect(A: str, B: str) -> str:
    """
    Calculates the intersection of two strings.
    :return: The intersection of the two strings.
    """
    res = ''
    for ch in A:
        if ch in B:
            res += ch
    return res


def difference(A: str, B: str) -> str:
    """
    Calculates the difference of two strings (A - B).
    :return: The difference of the two strings.
    """
    for ch in B:
        if ch in A:
            A = A.replace(ch, '')
    return A


def union(A: str, B: str) -> str:
    """
        Calculates the union of two strings (A union B), with no duplicate characters and sorted.
        :return: The union of the two strings.
        """
    return sort_string(A + B)


def strEqual(A: str, B: str) -> bool:
    """
    Checks if all letters of two strings are equal (not same order).
    :return: True if A == B, False otherwise.
    """
    return is_in(A, B) and is_in(B, A)


def CreateTable(R: str, decompositions: str):
    """
    Calculates the table to the lossless check of a decomposition.
     :param R: String of scheme.
     :param decompositions: String of decompositions. For example: 'ABC,CDE'
     :return: The table for lossless check.

     # >>> CreateTable('ABCDE', 'BE,ABC,AD')
     # [['b11', 'a2', 'b13', 'b14', 'a5'],
     #  ['a1', 'a2', 'a3', 'b24', 'b25'],
     #  ['a1', 'b32', 'b33', 'a4', 'b35']]
     """
    dec = decompositions.split(',')
    T = []
    for i in range(len(dec)):
        T.append([])
        for j in range(len(R)):
            if R[j] in dec[i]:  # If attribute is in
                T[i].append("a" + str(j + 1))
            else:
                T[i].append("b" + str(i + 1) + str(j + 1))
    return T


def ChaseTable(R: str, T, F: str):
    """
    Returns the complete chase table for a lossless decomposition check.
    :param R: String of scheme.
    :param T: Table generated in the CreateTable function.
    :param F: String of rules.
    :return: The completed chase table.

    # >>> ChaseTable('ABCDE', CreateTable('ABCDE', 'BE,ABC,AD'), 'A->BC,B->E,D->C,CD->AE')
    #  [['b11', 'a2', 'b13', 'b14', 'a5'],
    #   ['a1', 'a2', 'a3', 'b24', 'a5'],
    #   ['a1', 'a2', 'a3', 'a4', 'a5']]
    """
    attrDict = {}
    for i in range(len(R)):
        attrDict[R[i]] = i

    changed = True  # Check if there were any differences
    while changed:
        changed = False
        for rule in F.split(','):  # For every rule X->Y
            spl = rule.split('->')
            for t in range(len(T)):
                for s in range(t + 1, len(T)):  # Check every two lines.
                    for attr in spl[0]:  # Check if exist two lines with all attributes of X equal.
                        if T[t][attrDict[attr]] != T[s][attrDict[attr]] or s == t:
                            break

                    else:  # If there are lines with with all attributes of X equal:
                        for attr2 in spl[1]:  # Check if all attributes of Y is equal in those lines.
                            if T[t][attrDict[attr2]] != T[s][attrDict[attr2]]:
                                changed = True  # if not equal, if one is a-type, change the other to it as well.
                                if T[t][attrDict[attr2]][0] == 'a':
                                    T[s][attrDict[attr2]] = T[t][attrDict[attr2]]
                                else:  # if s[attrDict[attr]][0] == 'a'
                                    T[t][attrDict[attr2]] = T[s][attrDict[attr2]]

    return T


def LosslessDecomposition(R: str, decompositions: str, F: str) -> str:
    """
    Checks whether a decomposition is lossless or not.
    :param R: String of scheme.
    :param decompositions: String of decompositions. For example: 'ABC,CDE'
    :param F: String of rules.
    :return: "Lossless" if lossless, "Not lossless" otherwise.
    """
    T = CreateTable(R, decompositions)
    T = ChaseTable(R, T, F)
    for line in T:
        for attr in line:
            if attr[0] != 'a':
                break
        else:
            return "Lossless"

    return "Not lossless"


def DependencyPreserving(F: str, decompositions: str) -> (int, bool):
    """
    Counts how many dependencies from the F were preserved in a decomposition.
    :param F: String of rules.
    :param decompositions: String of decompositions. For example: 'ABC,CDE'
    :return: Count of dependencies preserved and if the decomposition is preserving dependencies.
    """
    dec = decompositions.split(',')
    preservedCount = 0
    for rule in F.split(','):
        _z = ''
        spl = rule.split('->')
        z = spl[0]  # z = x
        while z != _z and not is_in(spl[1], z):
            _z = z
            for de in dec:
                z = union(z, intersect(closure(F, intersect(z, de)), de))

        if is_in(spl[1], z):
            preservedCount += 1

    return preservedCount, preservedCount == len(F.split(','))


def sort_string(s: str) -> str:
    """
    Sorts a string and remove duplicate characters.
    :param s: The string to sort.
    :return: A sorted string.
    """
    return ''.join(sorted(set(s)))


def is_in(a: str, b: str) -> bool:
    """
    Checks if every character from the string 'a' is included in the string 'b'
    :return: True if a is in b, false otherwise.
    """
    for ch in a:
        if ch not in b:
            return False
    return True


def closure(F: str, attr: str) -> str:
    """
    Calculates the closure of given attribute(s).
    :param F: String of rules.
    :param attr: The attribute(s) to calculate closure of.
    :return: String representing the closure of the attribute(s).
    """
    clo = attr
    clot = ''
    while clo != clot:
        clot = clo
        for f in F.split(','):
            spl = f.split('->')
            if is_in(spl[0], clo):
                clo += spl[1]
            clo = ''.join(sorted(set(clo)))

    return clo


def ComputeMinimalCover(F: str) -> str:
    """
    Calculates the minimal cover of group of rules.
    :param F: String of rules.
    :return: Minimal cover of F as string.
    """
    F1 = ''
    for rule in F.split(','):
        spl = rule.split('->')
        for rightSplit in spl[1]:
            F1 += spl[0] + '->' + rightSplit + ','

    F1 = F1[:-1]

    for rule in F1.split(','):
        spl = rule.split('->')
        for leftSplit in spl[0]:
            if leftSplit in closure(F1, spl[0].replace(leftSplit, '')):
                F1 = F1.replace(spl[0], spl[0].replace(leftSplit, ''))
                spl[0] = spl[0].replace(leftSplit, '')

    Fz = ''
    while Fz != F1:
        Fz = F1
        rules = F1.split(',')
        for rule in rules:
            r = rule.split('->')
            FWithoutRule = F1.replace(rule + ',', '')
            FWithoutRule = FWithoutRule.replace(rule, '')
            if FWithoutRule[-1] == ',':
                FWithoutRule = FWithoutRule[:-1]

            if r[1] in closure(FWithoutRule, r[0]):
                rules.remove(rule)
                F1 = ','.join(rules)

    return F1


def isRule3NF(R: str, F: str, rule: str) -> bool:
    """
    Checks whether a rule is qualified by the rules of BCNF.
    :param R: String of scheme.
    :param F: String of rules.
    :param rule: The rule to check.
    :return: True if rule is qualified, False otherwise.
    """

    spl = rule.split('->')  # For X->Y
    if strEqual(closure(F, spl[0]), R):  # If X is super-key
        return True

    keys = All_Keys(R, F)
    for attr in spl[1]:
        if not (attr in spl[0] or  # If any attribute from Y is not in X
                any([attr in key for key in keys])):  # and is not part of key:
            return False

    return True


def is3NF(R: str, F: str) -> bool:
    """
    Checks whether a rule group is qualified by the rules of BCNF.
    :param R: String of scheme.
    :param F: String of rules.
    :return: True if rule group is qualified, False otherwise.
    """
    for rule in F.split(','):
        if not isRule3NF(R, F, rule):
            return False
    return True


def Find3NFDecomposition(R: str, F: str) -> str:
    """
    Finds a 3NF decomposition according to the 3NFDecomposition algorithm.
    :param R: String of scheme.
    :param F: String of rules.
    :return: String of 3NF decomposition and other possible keys.
    """
    res = ''
    g = ComputeMinimalCover(F)
    for rule in g.split(','):
        spl = rule.split('->')
        res += spl[0] + spl[1] + ','

    res = res[:-1]
    keys = All_Keys(R, F)
    if not any([is_in(key, sch) for sch in res.split(',') for key in keys]):
        res += ',' + keys[0]

    dictRes = []
    for sp in res.split(','):
        for sp1 in dictRes:
            if is_in(sp, sp1) and sp != sp1:
                break
        else:
            dictRes.append(sp)

    return ','.join(dictRes) + '\n' + 'Possible Keys:' + str(keys)


def isDecomposition3NF(F: str, decompositions: str) -> bool:
    """
    Checks whether a decomposition is 3NF or not.
    :param F: String of rules.
    :param decompositions: String of decompositions. For example: 'ABC,CDE'
    :return: True if 3NF, False otherwise.
    """
    for dec in decompositions.split(','):
        if len(dec) > 2:
            fr = ComputeDependenciesInProjection(F, dec)
            if not is3NF(dec, fr):
                return False

    return True


def isRuleBCNF(R: str, F: str, rule: str) -> bool:
    """
    Checks whether a rule is qualified by the rules of BCNF.
    :param R: String of scheme.
    :param F: String of rules.
    :param rule: The rule to check.
    :return: True if rule is qualified, False otherwise.
    """

    spl = rule.split('->')
    if strEqual(closure(F, spl[0]), R) or is_in(spl[1], spl[0]):
        return True
    return False


def isBCNF(R: str, F: str) -> bool:
    """
    Checks whether a rule group is qualified by the rules of BCNF.
    :param R: String of scheme.
    :param F: String of rules.
    :return: True if rule group is qualified, False otherwise.
    """
    for rule in F.split(','):
        if not isRuleBCNF(R, F, rule):
            return False
    return True


def powerset(s):
    """
        Returns all subsets of iterable.
        :param s: The iterable to generate all options from.
        :return: All subsets of the given iterable.
    """

    if len(s) <= 1:
        yield s
        yield []
    else:
        for item in powerset(s[1:]):
            yield [s[0]] + item
            yield item


def powerSet(iterable):
    """
    Returns all subsets of iterable.
    :param iterable: The iterable to generate all options from.
    :return: All subsets of the given iterable as list of strings.

    # >>> list(powerSet('ABC'))
    # ['', 'A', 'B', 'C', 'AB', 'AC', 'BC', 'ABC']
    """

    s = list(iterable)
    combination = powerset(s)
    lstCom = list(combination)
    return [''.join(c) for c in lstCom]


def ComputeDependenciesInProjection(F: str, Ri: str):
    """
    Calculates all dependencies in a projection (for general purpose).
    :param F: String of rules.
    :param Ri: String of projection to calculate dependencies for.
    :return: String of dependencies.
    """
    rules = []
    all_sub = powerSet(Ri)[:-1]
    all_sub.sort(key=lambda x: (len(x), x))  # Sort by size and alphabetically
    keys = []
    for sub in all_sub:
        if any([key in sub for key in keys]):
            continue

        rightSide = intersect(closure(F, sub), Ri)
        if strEqual(rightSide, Ri):
            keys.append(sub)

        rs = difference(rightSide, sub)
        if not any([rs == t[1] and is_in(t[0], sub) for t in rules]) and len(rs) != 0:  # If not already exist as
            rules.append((sub, rs))  # shorted version. For example: A -> C and AB -> C

    return ','.join(['->'.join(rule) for rule in rules])


def FindBCNFDecomposition(R: str, F: str):
    """
    Finds a BCNF decomposition according to the BCNFDecomposition algorithm.
    :param R: String of scheme.
    :param F: String of rules.
    :return: String of BCNF decomposition.
    """
    if len(R) == 2 or F == '':
        return R

    for rule in F.split(','):
        if not isRuleBCNF(R, F, rule):
            spl = rule.split('->')
            r1 = closure(F, spl[0])

            r2 = spl[0]
            for ch in R:
                if ch not in r1:
                    r2 += ch

            r2 = sort_string(r2)
            break
    else:
        return R

    Fr1 = ComputeDependenciesInProjection(F, r1)
    Fr2 = ComputeDependenciesInProjection(F, r2)

    return FindBCNFDecomposition(r1, Fr1) + ',' + FindBCNFDecomposition(r2, Fr2)


def isDecompositionBCNF(F: str, decompositions: str) -> bool:
    """
    Checks whether a decomposition is BCNF or not.
    :param F: String of rules.
    :param decompositions: String of decompositions. For example: 'ABC,CDE'
    :return: True if BCNF, False otherwise.
    """
    for dec in decompositions.split(','):
        if len(dec) > 2:
            fr = ComputeDependenciesInProjection(F, dec)
            if not isBCNF(dec, fr):
                return False

    return True


def main():
    curR = input("Enter the scheme as a string. Example: 'ABCDE'\n")
    curF = input("Enter the rules as a string. Example: 'A->BC,B->E,D->C,CD->AE'\n")
    print("""\n
0) Exit.
1) Calculate all keys of (R, F).
2) Calculate closure of attribute(s).
3) Check if decomposition is lossless.
4) Check how many dependencies are preserved in a composition.
5) Calculate minimal cover of F.
6) Calculate the 3NF decomposition of (R, F).
7) Calculate the BCNF decomposition of (R, F).
8) Check if (R, F) meets the requirements of 3NF.
9) Check if (R, F) meets the requirements of BCNF.
10) Compute dependencies in a given projection,
11) Check if decomposition meets the requirements of 3NF.
12) Check if decomposition meets the requirements of BCNF.
    """
          )

    action = Action(int(input('Enter your choice: ')))
    while True:
        if action == Action.EXIT:
            break

        elif action == Action.ALL_KEYS:
            print(All_Keys(curR, curF))

        elif action == Action.CLOSURE:
            tmp = input("Enter attribute(s) to calculate closure for. Example: 'AB'\n")
            print(closure(curF, tmp))

        elif action == Action.CHECK_LOSSLESS:
            tmp = input("Enter decomposition(s) for lossless check. Example: 'AB,BC,CDE'\n")
            print(LosslessDecomposition(curR, tmp, curF))

        elif action == Action.CHECK_DEPENDENCIES_PRESERVING:
            tmp = input("Enter decomposition(s) for dependency preserving check. Example: 'AB,BC,CDE'\n")
            count, flag = DependencyPreserving(curF, tmp)
            print(str(count) + '/' + str(len(curF.split(','))) + ' dependencies preserved!')
            print("Is the decomposition preserving dependencies? " + "Yes" if flag else "No")

        elif action == Action.MINIMAL_COVER:
            print(ComputeMinimalCover(curF))

        elif action == Action.CALC_3NF:
            print(Find3NFDecomposition(curR, curF))

        elif action == Action.CALC_BCNF:
            print(FindBCNFDecomposition(curR, curF))

        elif action == Action.CHECK_3NF:
            print(is3NF(curR, curF))

        elif action == Action.CHECK_BCNF:
            print(isBCNF(curR, curF))

        elif action == Action.DEPENDENCIES_PROJECTION:
            tmp = input("Enter decomposition to calculate dependency projection for. Example: 'AB'\n")
            print(ComputeDependenciesInProjection(curF, tmp))

        elif action == Action.CHECK_3NF_DECOMPOSITION:
            tmp = input("Enter decomposition(s) for 3NF check. Example: 'AB,BC,CDE'\n")
            print(isDecomposition3NF(curF, tmp))

        elif action == Action.CHECK_BCNF_DECOMPOSITION:
            tmp = input("Enter decomposition(s) for BCNF check. Example: 'AB,BC,CDE'\n")
            print(isDecompositionBCNF(curF, tmp))

        else:
            print("Wrong option. Please re-enter.")

        action = Action(int(input('\nEnter your choice: ')))


# print(ComputeDependenciesInProjection('D->BC,AD->EG,E->C,G->AD,CEG->B,BC->A', 'ABC'))
# print(All_Keys('ABC', 'AB->ABC,A->ABC,AC->ABC'))
# print()

def tests():
    curR = 'ABCDEG'
    curF = 'A->G,CD->E,GE->CD,E->B,B->ACG'
    assert All_Keys(curR, curF) == ['E', 'CD', 'BD']
    assert closure(curF, 'E') == 'ABCDEG'
    assert closure(curF, 'AB') == 'ABCG'
    assert LosslessDecomposition(curR, 'AG,CDE,EB,BA,BC', curF) == 'Lossless'
    assert LosslessDecomposition(curR, 'ABC,CDEG', curF) == 'Not lossless'
    assert DependencyPreserving(curF, 'AG,CDE,EB,BA,BC') == (5, True)
    assert DependencyPreserving(curF, 'ABC,CDEG') == (2, False)
    assert ComputeMinimalCover(curF) == 'A->G,CD->E,E->D,E->B,B->A,B->C'
    assert Find3NFDecomposition(curR, curF) == "AG,CDE,EB,BA,BC\nPossible Keys:['E', 'CD', 'BD']"
    assert FindBCNFDecomposition(curR, curF) == 'AG,ABC,BDE'
    assert is3NF(curR, curF) is False
    assert is3NF(curR, 'A->BCDEG') is True
    assert isBCNF(curR, curF) is False
    assert isBCNF(curR, 'A->BCDEG') is True


if __name__ == '__main__':
    # tests()
    main()
"""
    >>> curR = 'ABCDE'
    >>> curF = 'A->BC,B->E,D->C,CD->AE'
    
    >>> closure(curF, 'AB')
    'ABCDE'
    
    >>> closure(curF, 'B')
    'BE'
    
    >>> ComputeMinimalCover(curF)
    'A->B,A->C,B->E,D->A'
    
    >>> All_Keys(curR,curF)
    ['D']
    
    >>> print(Find3NFDecomposition(curR, curF))
    AB,AC,BE,DA
    Possible Keys:['D']
        
    >>> LosslessDecomposition(curR, 'BE,ABC,AD', curF)
    'Lossless'
    
    >>> print(LosslessDecomposition(curR, 'AC,CDE,BD', curF))
    'Not lossless'
    
    >>> IsDependencyPreserving(curF, 'BE,ABC,AD')
    True
    
    >>> DependencyPreservingCount(curF, 'BE,ABC,AD')
    4
    
    >>> IsDependencyPreserving(curF, 'AC,CDE,BD')
    False
"""
