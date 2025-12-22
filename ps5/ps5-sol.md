---
title: ALG Problem Set 5
header-includes: |
  \usepackage{ctex}
  \usepackage{amsthm}
  \usepackage{amsmath}
  \usepackage{algorithm}
  \usepackage[noend]{algpseudocode}
  \usepackage{float}
  \usepackage{caption}
  \algrenewcommand\algorithmiccomment[1]{\hfill// #1}
---
## Problem 1
考虑二分查找优化的插入排序。
\newcommand{\ta}[1]{\textsc{#1}}
\newcommand{\To}{\ \textbf{to}\ }
\newcommand{\Downto}{\ \textbf{downto}\ }
\begin{minipage}{\textwidth}
\ta{BinaryInsertionSort}$(A[1..n])$
\begin{algorithmic}[1]
\State $B[1..n] = $ array of pairs, initialized to $(\infty, 0)$
\State $cnt = 0$
\For{$i = 1 \To n$} \Comment{循环 1}
  \State $pos = \ta{LowerBound}(B, 1, cnt + 1, A[i])$
  \If{$B[pos].fst == A[i]$}
    \State $B[pos].snd = B[pos].snd + 1$
  \Else
    \For{$j = cnt \Downto pos$}
      \State $B[j + 1] = B[j]$
    \EndFor
    \State $B[pos] = (A[i], 1)$
    \State $cnt = cnt + 1$
  \EndIf
\EndFor
\State $i = 1$
\For{$j = 1 \To cnt$} \Comment{循环 2}
  \For{$\_ = 1 \To B[j].snd$}
    \State $A[i] = B[j].fst$
    \State $i = i + 1$
  \EndFor
\EndFor
\end{algorithmic}

\ta{LowerBound}($B, l, r, v$)
\begin{algorithmic}[1]
\While{$l < r$}
  \State $mid = \lfloor (l + r) / 2 \rfloor$
  \If{$B[mid].fst < v$}
    \State $l = mid + 1$
  \Else
    \State $r = mid$
  \EndIf
\EndWhile
\State \Return $l$
\end{algorithmic}
\end{minipage}

### 正确性

对于循环 1，考虑不变式：在第 $i$ 次循环开始时，$B[1..cnt]$ 存储了 $A[1..i-1]$ 中所有不同元素及其出现次数，且按元素值递增排序。

1. 初始化：循环开始前，$i=1$，$cnt=0$，$B$ 为空，符合不变式。

2. 保持：假设在第 $i$ 次循环开始时不变式成立。通过调用 \ta{LowerBound} 找到 $A[i]$ 在 $B$ 中的位置 $pos$。如果 $A[i]$ 已存在于 $B$ 中，则增加其计数；否则，将其插入到正确位置并更新 $cnt$。这样，$B[1..cnt]$ 仍然存储了 $A[1..i]$ 中所有不同元素及其出现次数，且按元素值递增排序。

### 时间复杂度分析

设 $A$ 中有 $k$ 个不同元素。4-12 行的循环 1 结束后，$cnt = k$。

1. 循环 1 共执行 $n$ 次，每次调用 \ta{LowerBound} 的时间为 $O(\lg cnt\le \lg k)$；
   其中有 $k$ 次插入，每次插入最坏要移动 $cnt\le k$ 个元素，总的移动次数为 $O(k^2)$；有 $n - k$ 次修改，总的修改时间为 $O(n)$。

2. 循环 2 结束后，$i$ 的值是 $n+1$，所以运行时间为 $O(n)$。

总运行时间为为 $n \times O(\lg k) + O(k^2) + O(n) + O(n) = O(n + n \lg k + k^2)$。
由于 $k = O(\lg n)$，运行时间为 $O(n\lg\lg n)$。

## Problem 2
\text{(a) MSD-基数排序(模板)}

\begin{minipage}{\columnwidth}
\ta{RadixStringSortRecursive}$(A[1..m], B, d)$
\begin{algorithmic}[1]
\State $buckets[a..z] = $ array of lists, initialized to empty lists
\State $result = $ empty list
\For{$i : B$}
  \If{$d > |A[i]|$}
    \State $result.append(i)$
  \Else
    \State $c = A[i][d]$
    \State $buckets[c].append(i)$
  \EndIf
\EndFor
\For{$c \in \{a, b, \ldots, z\}$ in order}
  \If{$buckets[c]$ is not empty}
    \State $result.extend($\ta{RadixStringSortRecursive}$(A, buckets[c], d + 1))$
  \EndIf
\EndFor
\State \Return $result$
\end{algorithmic}
\ta{RadixStringSort}$(A[1..m])$
\begin{algorithmic}[1]
\State $B = [1, 2, \ldots, m]$
\State \ta{RadixStringSortRecursive}$(A, B, 1)$
\State $C = $ array of length $m$
\For{$i = 1 \To m$}
  \State $C[i] = A[B[i]]$
\EndFor
\State \Return $C$
\end{algorithmic}
\end{minipage}

### 时间复杂度分析
设所有字符串的字符总数为 $n$，有 $m$ 个字符串。

1. \ta{RadixStringSort} 准备 $B$ 需要 $O(m)$ 时间，复制结果到 $C$ 需要 $O(n + m)$ 时间，下面说明调用 $\ta{RadixStringSortRecursive}$ 需要 $O(n + m)$ 时间，所以总时间为 $O(n + m)$，假设所有字符串非空，则 $m \le n$，总时间为 $O(n)$。

2. \ta{RadixStringSortRecursive} 的每次调用需要 $O(1)$ 时间初始化桶，然后对 $|B|$ 个字符串进行一次循环，时间为 $O(|B|)$。接下来对每个非空桶递归调用自己。返回的 $result$ 的列表满足 $|result| = |B|$。因此每次非递归调用的时间为 $O(|B|)$。

    对于深度为 $d$ 的所有调用，$B$ 两两不交，且 $\sum |B| = f(d) = |\{i:|A[i]|\ge d - 1|\}$

    所有递归调用的时间为 $O(\sum_{d=1}^{\infty} f(d) = \sum_{i=1}^m\sum_{d=0}^{\infty} [|A[i]|\ge d] = \sum_{i=1}^m (|A[i]| + 1)) = O(n + m)$。

---

\text{(b) 初始的想法 Trie（字典树）+ 前序遍历}

\begin{minipage}{\columnwidth}
\textsc{TrieStringSort}$(A[1..n])$
\begin{algorithmic}[1]
\State $trie = $ new Trie with root node
\For{$i = 1$ \textbf{to} $n$}
  \State \textsc{Insert}$(trie, A[i])$
\EndFor
\State $result = $ empty list
\State \textsc{PreorderTraversal}$(trie.root, \text{``''}, result)$
\State \Return $result$
\end{algorithmic}
\end{minipage}

\begin{minipage}{\columnwidth}
\textsc{Insert}$(trie, str)$
\begin{algorithmic}[1]
\State $cur = trie.root$
\For{each character $c$ in $str$}
  \If{$cur.children[c]$ is \textbf{null}}
    \State $cur.children[c] = $ new TrieNode
  \EndIf
  \State $cur = cur.children[c]$
\EndFor
\State $cur.count = cur.count + 1$ \Comment{标记字符串结束}
\end{algorithmic}
\end{minipage}

\begin{minipage}{\columnwidth}
\textsc{PreorderTraversal}$(node, path, result)$
\begin{algorithmic}[1]
\For{$i = 1$ \textbf{to} $node.count$}
  \State $result.append(path)$ \Comment{输出以 path 结尾的字符串}
\EndFor
\For{each character $c \in \{a, b, \ldots, z\}$ in order}
  \If{$node.children[c] \neq \textbf{null}$}
    \State path.append($c$)
    \State \textsc{PreorderTraversal}$(node.children[c], path, result)$
    \State path.pop() \Comment{回溯}
  \EndIf
\EndFor
\end{algorithmic}
\end{minipage}

### 正确性

1. **Trie 的性质**：在 Trie 中，从根到任意节点的路径代表一个字符串或者字符串前缀，该节点的 `count` 属性表示该字符串出现的次数。

2. **字典序**：对于任意两个字符串 $s_1$ 和 $s_2$，如果 $s_1 < s_2$（字典序），则在前序遍历中 $s_1$ 必然在 $s_2$ 之前被输出。

    理由：由于 $s_1 < s_2$，则要么 $s_1$ 是 $s_2$ 的真前缀，要么存在一个位置 $i$，使得 $s_1[1..i-1] = s_2[1..i-1]$ 且 $s_1[i] < s_2[i]$。若 $s_1$ 是 $s_2$ 的真前缀，则在 Trie 中，$s_1$ 对应的节点是 $s_2$ 对应节点的祖先节点，因此在前序遍历中先访问 $s_1$。若存在位置 $i$ 使得 $s_1[i] < s_2[i]$，则在 Trie 中，$s_1$ 和 $s_2$ 在第 $i$ 个字符处分叉，由于我们按字母顺序遍历子节点，必然先访问 $s_1$ 的路径。

### 时间复杂度分析

设所有字符串的字符总数为 $n$。

1. **插入阶段**：
   - 插入一个长度为 L 的字符串需要 O(L) 时间
   - 插入所有字符串的总时间为 $\sum_{i=1}^{k} L_i = n$，其中 k 是字符串数量
   - 时间复杂度：O(n)

2. **前序遍历阶段**：
   - 每个 Trie 节点最多被访问一次
   - Trie 中的节点总数 $\le n$（因为每个字符最多创建一个新节点）
   - 每个节点的处理时间为 O(26) = O(1)（遍历最多 26 个子节点）
   - 输出字符串的时间与字符串总长度成正比，为 O(n)
   - 时间复杂度：O(n)

总时间复杂度为 O(n) + O(n) = O(n)

## Problem 3

如果 F.Lake 教授宣称他的优先队列是基于比较的，那么他错了。

我们通过归约到排序问题来证明。假设存在这样一个数据结构，支持 \ta{Insert}、\ta{GetMax} 和 \ta{ExtractMax} 都在 $O(1)$ 最坏情况时间内完成。

基于这个假设，我们可以构造一个 $O(n)$ 时间的基于比较的排序算法：

\begin{minipage}{\textwidth}
\ta{Sort}$(A[1..n])$
\begin{algorithmic}[1]
\State $Q = $ new priority queue
\For{$i = 1 \To n$} \Comment{插入阶段}
  \State \ta{Insert}$(Q, A[i])$
\EndFor
\For{$i = n \Downto 1$} \Comment{提取阶段}
  \State $A[i] = $ \ta{ExtractMax}$(Q)$
\EndFor
\end{algorithmic}
\end{minipage}

### 时间复杂度分析
- 插入阶段：$n$ 次 \ta{Insert} 操作，每次 $O(1)$ 时间，总时间 $O(n)$

- 提取阶段：$n$ 次 \ta{ExtractMax} 操作，每次 $O(1)$ 时间，总时间 $O(n)$

- 总时间：$O(n) + O(n) = O(n)$

这与基于比较的排序算法的下界是 $\Omega(n \lg n)$ 矛盾。

因此，不可能存在一个(基于比较的)优先队列同时在 $O(1)$ 最坏情况时间内支持 \ta{Insert}、\ta{GetMax} 和 \ta{ExtractMax} 操作。

\begin{center}\begin{minipage}{0.6\textwidth}
\kaishu
如果他的优先队列不基于比较，那么他可能是对的。
（比如，元素是不超过 d 位的整数，那用 Trie 树可以在最坏 O(d)
 实现优先队列；van Emde Boas 树则可以做到查询 O(1)，修改 O(log d)。
如果 d 是常数，可以认为是 O(1)。）
\end{minipage}\end{center}

## Problem 4
\begin{description}
\item[(a)] 考虑该问题的决策树，每个叶子节点确定了一个匹配方案，即一个排列 $\pi$，表示螺栓 $i$ 与螺母 $\pi(i)$ 匹配。共有 $n!$ 种不同的匹配方案，这些方案两两互斥，必须全部包含在决策树的叶子节点中。
由于每次螺栓-螺母测试有 3 种可能的结果：螺母太大、太小或刚好匹配。因此，$k$ 次测试后最多有 $3^k$ 个叶子节点。

要唯一确定正确的匹配方案，必须满足：
$$3^k \ge n!$$

取对数得：
$$k \ge \log_3(n!) = \frac{\ln(n!)}{\ln 3}$$

根据斯特林公式，$\ln(n!) = n \ln n - n + \frac{\ln n}{2} + O(1) = \Theta(n \ln n)$，因此：
$$k = \Omega\left(\frac{n \ln n}{\ln 3}\right) = \Omega(n \log n)$$

所以在最坏情况下，至少需要 $\Omega(n \log n)$ 次螺栓-螺母测试才能匹配所有螺栓和螺母。

\item[(b)] 考虑这个新问题的决策树，每个叶子最多覆盖 $(n-n/2)! = (n/2)!$ 种不同的匹配方案。为了确保算法能处理所有可能的输入，决策树的叶子节点数必须满足：
$$3^k \ge \frac{n!}{(n/2)!}$$
即 $k\ge \log_3\frac{n!}{(n/2)!} = \log_3 n! - \log_3 (n/2)!$。
同样利用斯特林公式，有：
$$k = \frac{n \ln n - (n/2) \ln (n/2) + O(n)}{\ln 3} = \frac{n \ln n - (n/2)(\ln n - \ln 2) + O(n)}{\ln 3} = \frac{n \ln n + O(n)}{2\ln 3} = \Omega(n \log n)$$
所以在最坏情况下，仍然需要 $\Omega(n \log n)$ 次螺栓-螺母测试才能匹配 $n/2$ 对螺栓和螺母。
\end{description}

## [Bonus Problem]
充分性：我们设计一种算法，在 $n - 2 + \lceil \lg n \rceil$ 次比较内找到第二大元素。

首先，用类似淘汰赛的方式找到最大元素。将 $n$ 个元素两两配对，进行 $n/2$ 次比较，胜者进入下一轮。重复此过程，直到剩下一个元素，即最大元素。由于共淘汰 $n-1$ 个元素，每次比较淘汰一个元素，这个过程需要 $n - 1$ 次比较。

然后，我们在和最大元素直接比较过的元素 $M$ 中寻找次大元素，因为其他元素都至少间接输给最大元素和 $M$ 中的某个元素，不可能是第二大的。由于每个元素在每轮中最多比较一次(可能轮空)，最多共比较 $\lceil \lg n \rceil$ 次。这需要 $\lceil \lg n \rceil - 1$ 次比较。

\begin{minipage}{\textwidth}
\ta{FindSecondLargest}$(A[1..n])$
\begin{algorithmic}[1]
\State $(largest, M) = $ \ta{FindLargest}$(A, \{1, 2, \ldots, n\})$
\State \Return \ta{FindLargest}$(A, M).\text{fst}$
\end{algorithmic}
\ta{FindLargest}$(A[1..n], I \text{ : Set of indices})$
\begin{algorithmic}[1]
\State $lose = $ array of length $n$, initialized to $0$
\While {$|I| \ge 2$}
  \State $I' = $ empty set
  \State pair up elements in $I$ as $(i_1, j_1), (i_2, j_2), \ldots$
  \For {each pair $(i, j)$}
    \If {$A[I[i]] > A[I[j]]$}
      \State $I'.\text{add}(i)$
      \State $lose[j] = i$
    \Else
      \State $I'.\text{add}(j)$
      \State $lose[i] = j$
    \EndIf
  \EndFor
  \If {$|I|$ is odd}
    \State $I'.\text{add}($the unpaired element in $I)$
  \EndIf
  \State $I = I'$
\EndWhile
\State $largest = $ the only element in $I$
\State \Return $(largest, \{i : lose[i] = largest\})$
\end{algorithmic}
\end{minipage}

必要性：
\href{https://math.stackexchange.com/questions/1601/lower-bound-for-finding-second-largest-element}{敌手构造来自 ShreevatsaR 2019 年的修订版，他的论证仍然有问题，我的版本彻底修正了论证}。
\href{https://people.engr.tamu.edu/andreas-klappenecker/csce411-s19/csce411-lowerbound3.pdf}{令见 Andreas Klappenecker 2019 年的讲义}。二者本质相同。

构造这样一个敌手算法，敌手维护一个有向无环图 $G$，节点为 $1\cdots n$，边 $i \to j$ 表示 $A[i] > A[j]$。只要 $G$ 没有环，敌手就可以用拓扑排序产生一个符合 $G$ 的序关系。

敌手还维护一个 $w[i]$，初始化为 1。对每个询问 $i \neq j$：

i. 如果 $G$ 上有 $i \to^{*} j$ 或 $j \to^{*} i$ 的路径，敌手分别输出 $A[i] > A[j]$ 和 $A[j] > A[i]$。
ii. 否则，如果 $w[i] \ge w[j]$，敌手输出 $A[i] > A[j]$，并在 $G$ 上添加边 $i \to j$；否则输出 $A[j] > A[i]$，并添加边 $j \to i$。
iii. 添加边 $i \to j$ 后，更新 $w[i] = w[i] + w[j]; w[j] = 0$。

1. 这样决定比较结果显然不会产生环，因为添加边 $i \to j$ 表明没有 $j \to^{*} i$ 的路径。

2. 算法在结束时必然可以确定最大元素，即 $G$ 中只有一个节点的入度为 $0$。否则，若 $x\neq y$ 的入度都为 $0$，那么敌手在拓扑排序中第一个输出 $x$，第二个输出 $y$，或者交换顺序输出，均满足 $G$，从而有两种不同的第二大元素，算法出错。

3. 任意时刻都有 $\sum_i w[i] = n$：初始化时显然成立；每次添加边 $i \to j$ 时，$w[i]$ 增加 $w[j]$，而 $w[j]$ 变为 $0$，所以总和不变。设 $m_1$ 为最大元素，则最终 $w(m_1) = n, w(m') = 0, \forall m' \neq m_1$。

5. $m_1$ 至少直接比较了 $\lceil \lg n \rceil$ 次：每次涉及 $m_1$ 的比较最多使 $w(m_1)$ 翻倍，不涉及 $m_1$ 的比较则不变。而初始时 $w(m_1) = 1$，要使 $w(m_1) = n$，至少需要 $\lceil \lg n \rceil$ 次比较涉及 $m_1$。

6. 至少需要 $n-2$ 次不涉及 $m_1$ 的比较才能确定第二大元素 $m_2$：从 $G$ 中删去 $m_1$ 和其所有出边，剩下的图 $G'$ 中有且仅有一个入度为 $0$ 的节点 $m_2$。这需要所有其他 $n-2$ 个节点至少有一条入边，所以至少需要 $n-2$ 次不涉及 $m_1$ 的比较。

综上，任何算法在最坏情况下至少需要 $n - 2 + \lceil \lg n \rceil$ 次比较才能确定第二大元素。

## Problem 5
\begin{algorithmic}[1]
\For {$j=2 \To n$} \Comment{$n - 2 + 2 = n$}
  \State $key = A[j]$ \Comment{$n - 1$}
  \State $i = j - 1$ \Comment{$n - 1$}
  \While {$i>0 \land A[i] > key$} \Comment{$f(j) + 1$}
    \State $A[i+1] = A[i]$ \Comment{$f(j)$}
    \State $i = i-1$ \Comment{$f(j)$}
  \EndWhile
  \State $A[i+1] = key$ \Comment{$n - 1$}
\EndFor
\end{algorithmic}
设 $f(j)$ 为第 $j$ 次外循环中内循环执行的次数，则总运行时间为：
$$T(n) = c_1 n + (c_2 + c_4 + c_3 + c_7)(n-1) + \sum_{j=2}^n (c_4 + c_5 + c_6)f(j)
= C_1 n + C_2 \sum_{j=2}^n f(j) + C_3$$
$f(j)$ 的值取决于 $A[1..j-1]$ 中大于 $A[j]$ 的元素个数。即 $f(j) = \sum_{i=1}^{j-1} [A[i] > A[j]]$.
\begin{minipage}{\columnwidth}
设 $I(i, j) = [A[i] > A[j]]$，则 $E(I(i, j)) = \Pr\{A[i] > A[j]\} = 1/2$，因为 $A$ 是随机排列的。
\begin{flalign*}
E(T(n)) &= C_1 n + C_2 \cdot \sum_{j=2}^n E(f(j)) + C_3 &\\
 &= C_1 n + C_2 \cdot \sum_{j=2}^n \sum_{i=1}^{j-1} E(I(i, j)) + C_3 & \text{期望的线性性}\\
 &= C_1 n + C_2 \cdot \sum_{j=2}^n \sum_{i=1}^{j-1} \frac{1}{2} + C_3 &\\
 &= C_1 n + C_2 \cdot \sum_{j=2}^n \frac{j-1}{2} + C_3 &\\
 &= C_1 n + C_2 \cdot \frac{n(n-1)}{4} + C_3 &\\
 &= \boxed{\Theta(n^2)} &
\end{flalign*}
\end{minipage}

## Problem 6
\begin{description}
\item[(a)]\ta{LargestsA}$(A[1..n], i)$\\[0.5ex]
\begin{minipage}{\columnwidth}
\begin{algorithmic}
\State \ta{MergeSort}$(A)$
\State $B =$ array of length $i$
\For{$j = 1 \To i$}
  \State $B[j] = A[n - i + j]$
\EndFor
\State \Return B
\end{algorithmic}
\end{minipage}\\[2ex]
The asymptotic worst-case running time is $\Theta(n\lg n) + i = \boxed{\Theta(n\lg n)}$.

\item[(b)]\ta{LargestsB}$(A[1..n], i)$\\[0.5ex]
\begin{minipage}{\columnwidth}
\begin{algorithmic}
\State \ta{BuildMaxHeap}($A$)
\State $B =$ array of length $i$
\For{$k = i \Downto 1$}
  \State $B[k] = \ta{ExtractMax}(A)$
\EndFor
\State \Return B
\end{algorithmic}
\end{minipage}\\[2ex]
The asymptotic worst-case running time is $\Theta(n) + \sum_{k=1}^i \Theta(\lg (n - k + 1)) =
\Theta(n + \lg \frac{n!}{(n-i)!}) = \boxed{\Theta(n + i\lg n)}$.

\item[(c)]\ta{LargestsC}$(A[1..n], i)$\\[0.5ex]
\begin{minipage}{\columnwidth}
\begin{algorithmic}
\State $B = $ array of length $i$
\State $Ith = \ta{MedianOfMedians}(A, i)$
\For{$k = 1 \To n$}
  \If{$A[k] \ge Ith$}
    \State $B.append(A[k])$
  \EndIf
\EndFor
\State \ta{MergeSort}$(B)$
\State \Return $B$
\end{algorithmic}
\end{minipage}\\[2ex]
The asymptotic worst-case running time is $\Theta(n) + \Theta(i\lg i) = \boxed{\Theta(n + i\lg i)}$.
\end{description}