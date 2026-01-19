# MaxSum  CS2205-2025Fall 
 
## 算法描述
Monad 上的证明算法正确性：选择序列中互不相邻的一组元素使其和最大。
算法的输入是一个整数序列，算法求出一个子序列使得其中任意两个在原序列中互不相邻。以下是算法的 `monad` 描述：

```
Definition max_sum (l: list Z): program (Z * list Z) :=
  '(max1, ans1, _, _) <- list_iter
                           (fun n =>
                              fun '(max1, ans1, max2, ans2) =>
                                choice
                                  (assume (max1 <= max2 + n);;
                                   ret (max2 + n, ans1 ++ [n], max1, ans1))
                                  (assume (max1 >= max2 + n);;
                                   ret (max1, ans1, max1, ans1)))
                           l
                           (0, [], 0, []);;
  ret (max1, ans1).
```

该算法中 `max1` 表示目前为止能选出的子序列和最大值， `ans1` 表示取到这个最大值的子序列，`max2` 表示在不能取当前整数的情况下能选出的子序列和最大值， `ans2` 表示取到这个最大值的解。

## 第二档难度

证明算法的第一项确实是满足条件的子序列中子序列和的最大值。

于是定义并证明如下定理：
```
Theorem max_sum_value_correct :
  forall l,
    Hoare (max_sum l)
      (fun '(m, _) => max_value_spec l m).
```
我们在`MaxSum.v`中完成了这个定理的证明。

## 第三档难度

在上面的基础上证明，算法的第二项输出确实是一组使得和最大的可行方案。

于是定义并证明如下引理：
```
Theorem max_sum_full_correct :
  forall l,
    Hoare (max_sum l)
      (fun '(m, s) => max_sum_full_spec l m s).
```
我们在`MaxSum.v`中完成了这个定理的证明。

## 第四档难度

修改算法，并证明算法的输出是所有最优解中下标字典序最小的。

首先，我们定义两个索引列表 `list Z` 的严格字典序 $<_{\text{lex}}$

```
Fixpoint index_lex_lt (il1 il2: list Z) : Prop := 
  match il1, il2 with
    [], [] => False
    [], _ :: _ => True
    _ :: _, [] => False
    i1 :: il1', i2 :: il2' => 
      i1 < i2 \/ (i1 = i2 /\ index_lex_lt il1' il2')
  end.      
```

以上定义保证：空列表 `[]` $<_{\text{lex}}$ 任何非空列表；非空列表按首元素比较：若 `i1 < i2` 则 `il1` $<_{\text{lex}}$ `il2`；若 `i1 = i2` 则递归比较尾部。这是符合索引列表的标准字典序定义。

同时，我们定义字典序最小最优解的规范

```
Definition lex_min_spec (l: list Z) (m: Z) (s: list Z) (il: list Z) : Prop :=
  max_sum_full_spec l m s /\
  is_indexed_elements l il s /\
  non_adjacent_in il /\
  (forall s' il',
     feasiblee_set l s' -> 
     is_indexed_elements l il' s' -> 
     non_adjacent_in il' -> 
     sum s' = m -> 
     index_lex_lt il il' \/ il = il').
```

以上定义保证：四元组`(m, s, il)`满足：`(m, s)`是第三档难度中的完整最优解，`il`是`s`在`l`中的索引列表， `il`满足互不相邻，且对任意其他最优解`(s', il')`有`il`$<_{\text{lex}}$`il'`（即`il`是字典序最小的索引列表）。

在原算法的基础上，我们关于索引修改后算法，如下所示：

```
Definition max_sum_lex (l: list Z): program (Z * list Z * list Z) :=
  '(max1, ans1, il1, _, _, _, _) <- 
    list_iter
      (fun n =>
         fun '(max1, ans1, il1, max2, ans2, il2, idx) =>
           choice
             (assume (max2 + n > max1);; 
              ret (max2 + n, ans2 ++ [n], il2 ++ [idx], max1, ans1, il1, idx + 1))
             (choice
                (assume (max2 + n < max1);;
                 ret (max1, ans1, il1, max1, ans1, il1, idx + 1))
                (assume (max2 + n = max1);;
                  choice 
                    (assume (index_lex_lt (il2 ++ [idx]) il1);;
                     ret (max2 + n, ans2 ++ [n], il2 ++ [idx], max1, ans1, il1, idx + 1))
                    (assume (~ index_lex_lt (il2 ++ [idx]) il1);;
                     ret (max1, ans1, il1, max1, ans1, il1, idx + 1))
                )
             )
      )
      l
      (0, [], [], 0, [], [], 0);; 
  ret (max1, ans1, il1).
```

以上定义保证算法返回三元组`(最大和，最优解值列表，最优解索引列表)`，关键修改在于：状态扩展为七元组`(m1, a1, i1, m2, a2, i2, idx)`，其中`i1`, `i2`是索引列表，`idx`是当前元素索引；在`max2 + n = max1`时，比较`i2 ++ [idx]`与`i1`的字典序，选择更小者。

根据以上算法的定义，我们给出循环不变式：

```
Definition max_sum_lex_inv (done: list Z) ... : Prop := ...
```

以上定义保证：处理完前缀`done`之后，状态满足`idx = length done`（索引计数正确），`(m1, a1, i1)`是`done`的字典序最小最优解（满足`lex_min_spec`的前三项+字典序最小性），`(m2, a2, i2)`是`removelast done`的字典序最小最优解（或空列表时为`(0, [], [])`）。这是归纳证明的核心，确保每一步状态均满足字典序最小性。

但是需要注意的是，上述算法对于一般的整数序列并不一定成立。比如说考虑序列`[1, 2, 3, 0, 0, 0, 4]`，前 5 个数和前 6 个数组成的序列的最大和的最小索引均是`[0, 2]`，但是完整序列的最大和的最小索引是`[0, 2, 4, 6]`，也就是说，原来的最小索引加上一个数后不一定仍然是最小索引。

为了排除这种情况，需要限制整数序列中的所有元素均大于0。此时由于最大和的序列中取到的元素一定为正，可以保证所有和最大的序列不存在包含关系（包含关系指的是一个索引序列是另一个索引序列的前缀）。在递推的时候，在两个和最大的索引序列后添加一个相同的索引，可以保证二者的字典序关系保持不变，进而保证了算法的正确性。

我们在`MaxSum.v`中完成了第四档难度的大部分证明，但是在索引序列递推处存在部分引理没能证明。代码中的几处`admit`对应的情况非常类似，都是关于字典序保持不变的证明。其余部分的证明我们均已完成，希望老师点评与指导。

接下来简单介绍我们在证明第四档难度的过程中定义并证明一些辅助引理：

* `proof_il'_nil`：证明空列表`[]`的唯一可行解是`s' = []`，其索引列表必为`[]`，用于处理归纳基础时，确保索引列表正确。

* `idx_eq_zero`：证明空列表`[]`长度为 0 ，故初始索引`idx = 0`，验证不变式在基础情况时成立。

* `In_0_non_adjacent`：证明单元素索引列表`[0]`满足互不相邻（只有一个元素，无相邻对），验证单元素解的可行性。

* `is_indexed_elements_restrict`：证明若`s`是`l ++ [x]`的子序列，且其索引均在`l`范围内，则`s`也是`l`的子序列，以确保在“不取新元素”的分支中，确保旧解`ans1`仍是新列表的子序列。

* `in_singleton`：证明单元素列表的成员关系等价于相等，简化索引列表的推理，如`[0]`中只有元素`0`。

* `max_sum_full_spec_inv`：证明`max_sum_full_spec`蕴含其三个组成部分，满足`max_value_spec`, `feasible_set`, `sum`。

* `feasible_single`：证明单元素列表`[x]`的可行解是`[x]`，其索引是`[0]`，用于处理单元素输入的基础情况。

* `max_value_spec_single_positive`：证明若`x > 0`则`[x]`的最大和必为`x`（取该元素本身），用于在`all_positive`的假设下单元素解必取该元素。

* `Zlength_removelast`：证明非空列表去掉末尾元素后长度减 1，用于维护索引计数器`idx`与列表长度的一致性。

* `max_sum_lex_inv_single_positive`：证明当输入为`[x]`且`x > 0`时，算法状态`(x, [x], [0], 0, [], []. 1)`满足不变式，关键步骤为取`x`（因`x > 0 = max1`），新索引列表为`[0]`（因`idx = 0`），且`ans2 = []`, `il2 = []`（因`removelast [x] = []`），用于验证归纳基础。

其他单元素引理（`max_sum_lex_inv_single_case`, `max_sum_lex_inv_contradiction_case`, `max_sum_lex_inv_valid_case`）：覆盖了单元素输入的所有分支（`x < max1`, `x = max1`且字典序比较），完备处理了归纳基础情况。

* `max_sum_lex_inv_extend_case`：证明当`max2 + x > max1`时，取新元素`x`，新状态满足不变式，其中的关键在于验证可行性，即`ans2 ++ [x]`是`(d0::drest)++[x]`的可行解（需`feasible_set_app_x_r`），以及字典序最小性（因和更大，无需比较字典序），用于处理“必须取”的分支。

* `max_sum_lex_inv_preserve_when_not_taken`：证明当`max2 + x < max1`时，不取`x`，旧解`ans1`仍是新列表的最优解，其中的关键在于验证可行性（由`feasible_set_preserved`保证），以及字典序最小性（因和更大，旧解仍最优且字典序最小），用于处理“必须不取”的分支。

* `max_sum_lex_inv_eq_case`, `max_sum_lex_inv_eq_nlex_case`：证明(`eq_case`)当和相等且`il2 ++ [idx]`$<_{\text{lex}}$`il1`时，取新解，(`eq_nlex_case`)否则保留旧解。

以上四个引理均为索引序列递推过程（归纳步骤核心）的引理，我们在证明字典序保持不变的过程中遇到了一些困难，存在着一些情况相似的`admit`情况。

* `max_sum_lex_correct`：算法正确性验证，定义如下：
```
Theorem max_sum_lex_correct: 
  forall l, 
    all_positive l -> 
    Hoare (max_sum_lex l) 
      (fun '(m, s, il) => lex_min_spec l m s il).
```
以上定义确保：在所有元素为正 (`all_positive l`) 的假设下，`max_sum_lex`返回字典序最小的最优解。其中，我们需要`all_positive`简化基础情况（单元素必取），以避免反复取`0`导致的复杂讨论。注意，在保证上述四个索引序列递推过程的引理正确的情况下，由于`max_sum_lex_correct`覆盖所有分支，最终可以验证正确性。


