---
title: ALG Problem Set 6
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
只要遍历树即可。
\newcommand{\ta}[1]{\textsc{#1}}
\newcommand{\To}{\ \textbf{to}\ }
\newcommand{\Downto}{\ \textbf{downto}\ }
\begin{minipage}{\textwidth}
\ta{Traversal}$(root)$
\begin{algorithmic}[1]
\If{$root = null$}
    \State \Return
\EndIf
\State \textbf{print} $root$
\State \ta{Traversal}$(root.left)$
\State \ta{Traversal}$(root.right)$
\end{algorithmic}
\end{minipage}

上述算法按前序遍历的顺序打印出左儿子-右兄弟表示的多叉树中所有结点。时间复杂度为$O(n)$。

## Problem 2
\begin{description}
\item[(a)] 从根节点出发，沿着每个节点的重儿子（即子树规模最大的儿子）一直走到底所经过的路径称为该二叉树的重链。

对任意二叉树，任取一条重链，按照深度从大到小的顺序将重链上的节点重新编号为 $1,2,\ldots,k$。
设 $c_i$ 为以 $i$ 为根的子树的节点个数。

由于 $c_i$ 单调递增, $c_1 = 1 \le \lfloor n/2\rfloor < n = c_k$，存在某个 $j$ 使得 $c_j \le \lfloor n/2 \rfloor$ 且 $c_{j+1} > \lfloor n/2 \rfloor$。编号为 $j+1$ 的节点的重儿子规模不超过 $n/2$，另一个儿子规模也不超过 $n/2$，删去该节点后剩余的树的规模为 $n - c_{j+1} < \lceil n/2 \rceil$，也不超过 $n/2$。因此重心存在，且编号为 $j+1$ 的节点即为所求的重心。

\item[(b)] (a) 确保了总能在重链上找到重心。

\begin{minipage}{\textwidth}
\ta{ComputeSize}$(node)$
\begin{algorithmic}[1]
\If{$node = null$}
  \State \Return $0$
\EndIf
\State $node.size = 1 + \ta{ComputeSize}$(node.left) + \ta{ComputeSize}$(node.right)$
\end{algorithmic}
\end{minipage}
\begin{minipage}{\textwidth}
\ta{FindCentroidAux}$(root, n)$
\begin{algorithmic}[1]
\If{$root = null$}
  \State \Return $null$
\EndIf
\If{$root.left \neq null$ \textbf{and} $root.left.size > \lfloor n/2 \rfloor$}
  \State \Return \ta{FindCentroidAux}$(root.left)$
\EndIf
\If{$root.right \neq null$ \textbf{and} $root.right.size > \lfloor n/2 \rfloor$}
  \State \Return \ta{FindCentroidAux}$(root.right)$
\EndIf
\State \Return $root$
\end{algorithmic}
\ta{FindCentroid}$(root)$
\begin{algorithmic}[1]
\State $n = \ta{ComputeSize}(root)$
\State \Return \ta{FindCentroidAux}$(root, n)$
\end{algorithmic}
\end{minipage}

正确性(简要说明)：在\ta{FindCentroidAux} 开始时，传入的 $root$ 节点的子树大小 size 满足 $n/2<size\le n$。如果 $root$ 的某个儿子的子树大小 $> \lfloor n/2 \rfloor$，则该儿子必定是重儿子，因此该儿子的子树中必有重心。否则 $root$ 即为重心。

算法最多遍历每个节点两次，时间复杂度为$O(n)$。
\end{description}

## Problem 3
**(a)**
```
           I
       /       \
      Q         O
     / \     /     \
    J   V   T       K
   / \     / \     / \
  H   L   S   B   C   A
     / \     / \     / \
    E   M   R   Z   &   X
           / \     / \
          G   Y   F   W
                 / \
                P   N
                   / \
                  U   
```
**(b)**
```
  1    1
 /  和  \
2        2
```
的前序遍历都为 1 2 后序遍历都为 2 1，所以不能根据前序遍历和后序遍历唯一确定任意二叉树。
\begin{description}
\item[(c)] 递归建树。

\begin{minipage}{\textwidth}
\ta{BuildTree}$(preorder, postorder)$
\begin{algorithmic}[1]
\State $rootValue = preorder[1]$
\State $root = \text{new TreeNode}(rootValue)$
\If{$|preorder| = 1$}
  \State \Return $root$
\EndIf
\State $leftRootValue = preorder[2]$
\State $leftSubtreeEnd = \text{index of } leftRootValue \text{ in } postorder$
\State $root.left = \ta{BuildTree}(preorder[2:leftSubtreeEnd+1], postorder[1:leftSubtreeEnd])$
\State $root.right = \ta{BuildTree}(preorder[leftSubtreeEnd+2:], postorder[leftSubtreeEnd+1:-1])$
\State \Return $root$
\end{algorithmic}
\end{minipage}
\end{description}

正确性：若 $|preorder| > 1$，则子树非叶子节点。根据满二叉树的性质，左子树的根节点为 $preorder[2]$。根据前序遍历和后序遍历的定义，可以划分出左子树和右子树的前序遍历和后序遍历，递归地建造左右子树并连接到根节点上。

时间复杂度：每次递归中寻找左子树根节点在后序遍历中的位置需要 $O(n)$ 时间，递归深度为 $O(n)$，最坏时间复杂度为 $O(n^2)$。对于尽可能往右偏的满二叉树，会达到最坏时间复杂度 $\Theta(n^2)$。

## Bonus Problem
考虑 Morris 遍历。在遍历过程中会修改树的结构，但最终会恢复原状。算法如下：

0. $u = root, u$ 非空时重复以下步骤：
1. 若 $u$ 无左儿子，则访问 $u$ 并令 $u = u.right$。
2. 否则，在 $u$ 的左子树中找到 $u$ 在左子树中的最右节点 $v$。
   1. 若 $v.right = null$，则将 $v.right$ 指向 $u$，并访问 $u$，令 $u = u.left$。
   2. 若 $v.right = u$，则将 $v.right$ 置为 $null$，并令 $u = u.right$。

正确性：令 $T[x]$ 表示二叉树 $T$ 附带最右节点的右儿子指向 $x$ 的修改。

下面证明 Morris 在 $u$ 指向 $T[x]$ 时，会访问 $T$ 的所有节点，访问结束后 $u = x$。

对树的结构进行归纳：

1. 若 $T$ 为空，显然成立。
2. 若 $T[x]$ 非空，设 $T$ 的根节点为 $r$，左子树为 $L$，右子树为 $R$。
    注意到若 $R$ 为空，则 $T[x] = (L, r[x], E)$，否则，则 $T[x] = (L, r, R[x])$
    1. 若 $L$ 为空，则 Morris 访问 $r$ 并
        1. 若 $R$ 为空，访问结束，$u = x$。
        2. 若 $R$ 非空，则修改 $u$ 指向 $R[x]$。根据归纳假设，Morris 随后会访问 $R$ 的所有节点，访问结束后 $u = x$。
    2. 若 $L$ 非空，则访问 $r$；修改 $L$ 为 $L[r]$ 并访问。根据归纳假设，Morris 会访问 $L$ 的所有节点，访问结束后 $u = r$。随后 Morris 发现 $L$ 的最右节点 $v$ 的右儿子指向 $r$，将 $v.right$ 置为 $null$ 并令 $u = R$。根据 2.1.* 的分析，Morris 会访问 $R$ 的所有节点，访问结束后 $u = x$。

所以 Morris 在 $u = root[null]$ 时，会访问 $T$ 的所有节点，访问结束后 $u = null$，循环终止。

时间复杂度：每个有左儿子的节点会经过两次，其他节点经过一次，总次数为 $O(n)$。对于不同的节点，寻找最右子节点经过的路径互不重叠，因此寻找最右子节点的*总*时间为 $O(n)$。总时间复杂度为 $O(n)$。

## Problem 4
**(a)**
```
     1          2
T1 =  \ , T2 = /
       2      1
```
T1 已经不能再右旋了，所以 T1 无法通过右旋变成 T2。

**(b)**
我们证明一颗 $n$ 个节点的二叉树最多可以进行 $O(n^2)$ 次右旋。
定义路径的右深度为路径经过的右儿子节点的个数。定义树的右旋程度为根节点到所有节点的路径的右深度之和。
对于一次右旋：
```
    b           a
   / \    RR   / \
  a  t3  ---> t1  b
 / \             / \
t1 t2           t2 t3
```
旋转可能影响 5 类节点的右深度：

1. t1 中的节点，右深度不变；
2. t2 中的节点，右深度不变；
3. t3 中的节点，右深度 +1;
4. 节点 a，右深度不变；
5. 节点 b，右深度 +1。

因此，每次右旋，树的右旋程度增加了 $|t3| + 1 \ge 1$。

一颗 $n$ 个节点的二叉树的右旋程度不超过 $n^2$，因为每条路径的右深度不超过 $n-1$，共有 $n-1$ 条路径。

若 $T_1$ 可以右旋成 $T_2$，则一定在 $O(n^2)$ 次右旋内完成。

\begin{center}\begin{minipage}{0.6\textwidth}
\kaishu
实际上，我们的估计在渐进意义下是紧的。考虑 $T_1$ 是所有节点都只有左儿子的链状树，$T_2$ 是所有节点都只有右儿子的链状树。从 $T_1$ 变到 $T_2$ 需要进行 $\sum_{i=1}^{n-1} i = \frac{n(n-1)}{2} = \Theta(n^2)$ 次右旋。
\end{minipage}\end{center}

## Problem 5
对 $T_1$ 的根节点重复左旋，直到根节点没有右儿子。把 $T_2$ 挂到此时根节点的右儿子上。
```
T1 = x1
    /  \
   L1  x2
       / \
      L2 x3
         / \
       ... xk
          /
         Lk
Tmerge = xk
        /  \
    x(k-1) T2
      /  \
    ...  Lk
    /
   x1
  /  \
 L1  L2
```
\vspace{1em}
\begin{minipage}{\textwidth}
\ta{LeftRotate}$(T)$
\begin{algorithmic}[1]
\If{$T.right = null$}
  \State \Return $T$
\EndIf
\State $newRoot = T.right$
\State $T.right = newRoot.left$
\State $newRoot.left = T$
\State \Return $newRoot$
\end{algorithmic}
\ta{MergeBST}$(T_1, T_2)$
\begin{algorithmic}[1]
\While{$T_1.right \neq null$}
  \State $T_1 = \ta{LeftRotate}(T_1)$
\EndWhile
\State $T_1.right = T_2$
\State \Return $T_1$
\end{algorithmic}
\end{minipage}
部分正确性：$T_1$ 中的所有键值均小于 $T_2$ 中的所有键值。左旋保持 BST 的元素和性质，因此经过若干次左旋后，$T_1$ 仍然是一个 BST，且根节点的值小于 $T_2$ 所有节点的值。将 $T_2$ 挂到 $T_1$ 的根节点的右儿子上后，仍然满足 BST 的性质，因此合并后的树仍然是一个 BST。

停止：每次循环将 $T_1$ 的右子树的高度至少减少 $1$，$T_1$ 的高度 $\le h$，因此循环至多执行 $h$ 次，最终 $T_1$ 的右子树为空，循环终止。

算法时间复杂度为 $O(h)$：左旋 $\le h$ 次，每次左旋 $O(1)$ 时间，合并 $O(1)$ 时间，总时间 $O(h)$。

---
(原始的想法)
合并两个 BST 的过程可以递归地进行。设两个 BST 分别为 $T_1$ 和 $T_2$, $T_1$ 中的所有键值均小于 $T_2$ 中的所有键值。合并过程如下：

1. 若 $T_1$ 为空，则返回 $T_2$。
2. 若 $T_1$ 不为空，则取 $T_1$ 中键值最大地节点 $x$，$x$ 没有右儿子，$x$ 的左儿子记为 $T_x$。删去 $x$ 后，$T_1$ 分割为 $T_1'$ 和 $T_x$。递归地将 $T_1'$ 和 $T_x$ 合并，得到 $T'$。将 $x$ 作为根节点，$T'$ 作为左子树，$T_2$ 作为右子树，构造出新的 BST 并返回。

我们用 coq 实现了上述合并算法并证明了正确性 \href{https://github.com/top-mind/alg2025_nju/blob/master/bst.v}{[代码链接]}。