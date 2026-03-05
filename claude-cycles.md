# Claude's Cycles

**Don Knuth, Stanford Computer Science Department**

*(28 February 2026; revised 04 March 2026)*

Shock! Shock! I learned yesterday that an open problem I'd been working on for several weeks had just
been solved by Claude Opus 4.6 --- Anthropic's hybrid reasoning model that had been released three weeks
earlier! It seems that I'll have to revise my opinions about "generative AI" one of these days. What a joy
it is to learn not only that my conjecture has a nice solution but also to celebrate this dramatic advance in
automatic deduction and creative problem solving. I'll try to tell the story briefly in this note.

Here's the problem, which came up while I was writing about directed Hamiltonian cycles for a future
volume of *The Art of Computer Programming*:

> Consider the digraph with m<sup>3</sup> vertices *ijk* for 0 &le; i, j, k < m, and three arcs from
> each vertex, namely to i<sup>+</sup>jk, ij<sup>+</sup>k, and ijk<sup>+</sup>, where i<sup>+</sup> = (i+1) mod m. Try to find
> a general decomposition of the arcs into three directed m<sup>3</sup>-cycles, for all m > 2.

I had solved the problem for m = 3, and asked for a generalization as part of the answer to an exercise in
[3]. My friend Filip Stappers rose to the challenge, and empirically discovered solutions for 4 &le; m &le; 16;
therefore it became highly likely that the desired decompositions do exist, except when m &le; 2.

Indeed, it was Filip who had the gumption to pose this question to Claude, using exactly the wording
above. He also gave guidance/coaching, instructing Claude to summarize its ongoing progress:

> **\*\* After EVERY exploreXX.py run, IMMEDIATELY update this file [plan.md]
> before doing anything else. \*\*** No exceptions. Do not start the next exploration
> until the previous one is documented here.

And Claude's plan of attack was quite admirable. First it reformulated the problem: "Need sigma: Z<sub>m</sub><sup>3</sup> &rarr; S<sub>3</sub>,
assigning a permutation of {0, 1, 2} at each vertex; cycle c at vertex v goes in direction sigma(v)[c]. Each
resulting functional digraph must be a single Hamiltonian cycle." Then it tried for a simple answer: "'If
sigma is cyclic, i.e. f<sub>c</sub>(v) = (c+g(v)) mod 3 for some g : Z<sub>m</sub><sup>3</sup> &rarr; Z<sub>3</sub>, then we only need one function g. Tested
linear g = (a&middot;i+b&middot;j+c&middot;k) mod 3 and quadratic variants. No linear or simple quadratic g works."

Claude's second exploration was what it called a DFS search attempt (depth-first search): "Attempted
brute-force DFS over sigma assignments for m = 3 (6<sup>27</sup> search space). Too slow without good pruning."

Thirdly, it tried what it called 2D serpentine analysis: "Key 2D result: The pattern [0<sup>m&minus;1</sup>1]<sup>m</sup> gives a
Hamiltonian cycle in Cay(Z<sub>m</sub><sup>2</sup>, {e<sub>0</sub>, e<sub>1</sub>}) for m = 3. Its complement also works, giving a valid 2D decomposition." This is really impressive! First Claude recognized the digraph as a so-called Cayley digraph with two
generators, traditionally called e<sub>0</sub> and e<sub>1</sub>; a mathematician will understand that the arcs act as a group on
m<sup>2</sup> vertices, where e<sub>0</sub> increments the first component while e<sub>1</sub> increments the second. Then it formulated
the cycle symbolically for general m, although for some reason it still said that it was only looking at m = 3.
And it decided to call this a "serpentine pattern"!

Exploration number 4 constructed the "3D serpentine pattern" [0<sup>m&minus;1</sup>1]<sup>m&minus;1</sup>[0<sup>m&minus;1</sup>2]<sup>m</sup>. (That's a typographic error for [[0<sup>m&minus;1</sup>1]<sup>m&minus;1</sup>0<sup>m&minus;1</sup>2]<sup>m</sup>. It's a classical sequence called the "modular m-ary Gray code" on
page 299 of [2].) After deleting this cycle from the graph, Claude looked at the remaining 2-regular digraph
and found that it has "rigid structure making decomposition difficult."

Nevertheless, exploration number 5 analyzed that residual digraph, finding some cycles. Unfortunately
they didn't work out.

Back to the drawing board. Several other approaches were tried, for example looking at the choices
to be made at vertices that lie on the hyperplane where i+j+k is congruent to &minus;1. Nothing promising
showed up until exploration number 15, which introduced what Claude called a fiber decomposition: "The
quotient map &pi;(i, j, k) = i+j+k mod m maps all arcs from fiber F<sub>s</sub> to F<sub>s+1</sub>. The digraph is layered. In fiber
coordinates (i, j) with k = (s&minus;i&minus;j) mod m."

Using those fiber coordinates, the problem could now be reformulated as choosing, for each (i, j, s), a
permutation of the three operators that shift (i, j) by either (1, 0) or (0, 1) or (0, 0). "Tried sigma depending
only on fiber index s (rotation by s): gives the (i+j+k) mod 3 pattern which doesn't work. Random local
search found solutions for m = 3 but no general pattern emerged."

Exploration 18 "implemented the full fiber framework as executable code. Exhaustive backtracking for
m = 3 found a valid decomposition in 0.1s (10932 nodes)." In this solution the permutation sigma was the
same for all (i, j) in fiber s = 0. A similarly "uniform" fiber was found for m = 4 by simulated annealing, as
part of exploration 20.

In exploration 21, Claude realized that the 2D serpentine function "Q(i, j) = (i+1, j) if i+j &ne; m&minus;1
mod m, else (i, j+1)" had nice properties. It looked promising when a uniform choice is made at fiber 0 and
a version of the serpentine at all other fibers, if and only if m is odd.

That triggered a bunch of experiments with simulated annealing "at scale"; but all was for naught. The
conclusion after exploration 25 was "SA can find solutions but cannot give a general construction. Need
pure math."

So now Claude put on a new thinking cap. At one point it said to itself, "Maybe the right framing is:
don't think in fibers, think directly about what makes a Hamiltonian cycle."

There was a near miss at exploration number 27. "Take the 3D serpentine for cycle 0, apply cyclic
coordinate rotation to get cycles 1 and 2: d<sub>1</sub>(i, j, k) = (d<sub>0</sub>(j, k, i)+1) mod 3; d<sub>2</sub>(i, j, k) = (d<sub>0</sub>(k, i, j)+
2) mod 3; all three are individually Hamiltonian for every m = 3 .. 9 tested! Only 3(m&minus;1) out of m<sup>3</sup> vertices
have conflicts. all lie on the hyperplane i+j+k = m&minus;1 mod m."

Unfortunately, those conflicts couldn't be resolved. Exploration 29 proved that many plausible scenarios
were in fact impossible. "This kills the 'single-hyperplane + rotation' approach entirely. . . . We must allow
the direction function to use different values across a rotation orbit."

But, aha. Exploration 30 went back to the solution found by SA in exploration 20 and noticed that
the choice at each fiber depends on only a single coordinate: s = 0 only on j; s = 1 and s = 2 only on i.
This led to a concrete construction (exploration 31), in the form of a Python program, which produced valid
results for m = 3, 5, 7, 9, and 11 --- hooray! "All three cycles are Hamiltonian, all arcs are used, perfect
decomposition!"

Here is a simplification of that Python program, converted into C form:

```c
int c, i, j, k, m, s, t;
char *d;
for (c = 0; c < 3; c++) {
    for (t = i = j = k = 0; ; t++) {
        printf ("%x%x%x ", i, j, k);
        if (t == m*m*m) break;
        s = (i+j+k) % m;
        if (s == 0) d = (j == m-1? "012" : "210");
        else if (s == m-1) d = (i == 0? "210" : "120");
        else d = (i == m-1? "201" : "102");
        switch (d[c]) {
        case '0': i = (i+1) % m; break;
        case '1': j = (j+1) % m; break;
        case '2': k = (k+1) % m; break;
        }
    }
    printf ("\n");
}
```

Filip Stappers tested Claude's Python program for all odd m between 3 and 101, finding perfect decompositions each time. Thus he concluded, quite reasonably, that the problem was indeed solved for odd
values of m. And he quickly sent me the shocking news.

Of course, a rigorous proof was still needed. And the construction of such a proof turns out to be quite
interesting. Let's look, for example, at the first cycle that is printed; we must prove that it has length m<sup>3</sup>.

The rule for that cycle is nontrivial, yet fairly simple: Let s = (i+j+k) mod m.

- When s = 0, bump i if j = m&minus;1, otherwise bump k.
- When 0 < s < m&minus;1, bump k if i = m&minus;1, otherwise bump j.
- When s = m&minus;1, bump j if i > 0, otherwise bump k.

("Bump" means "increase by 1, mod m.") Hence in the special case m = 3 that cycle is

> 022 &rarr; 002 &rarr; 000 &rarr; 001 &rarr; 011 &rarr; 012 &rarr; 010 &rarr; 020 &rarr; 021 &rarr;
> 121 &rarr; 101 &rarr; 111 &rarr; 112 &rarr; 122 &rarr; 102 &rarr; 100 &rarr; 110 &rarr; 120 &rarr;
> 220 &rarr; 221 &rarr; 201 &rarr; 202 &rarr; 200 &rarr; 210 &rarr; 211 &rarr; 212 &rarr; 222 &rarr; 022.

And in the special case m = 5 it's

> 042&rarr;002&rarr;012&rarr;022&rarr;023&rarr;024&rarr;034&rarr;044&rarr;004&rarr;000&rarr;001&rarr;011&rarr;021&rarr;
> 031&rarr;032&rarr;033&rarr;043&rarr;003&rarr;013&rarr;014&rarr;010&rarr;020&rarr;030&rarr;040&rarr;041&rarr;
> 141&rarr;101&rarr;111&rarr;121&rarr;131&rarr;132&rarr;142&rarr;102&rarr;112&rarr;122&rarr;123&rarr;133&rarr;143&rarr;
> 103&rarr;113&rarr;114&rarr;124&rarr;134&rarr;144&rarr;104&rarr;100&rarr;110&rarr;120&rarr;130&rarr;140&rarr;
> 240&rarr;200&rarr;210&rarr;220&rarr;230&rarr;231&rarr;241&rarr;201&rarr;211&rarr;221&rarr;222&rarr;232&rarr;242&rarr;
> 202&rarr;212&rarr;213&rarr;223&rarr;233&rarr;243&rarr;203&rarr;204&rarr;214&rarr;224&rarr;234&rarr;244&rarr;
> 344&rarr;304&rarr;314&rarr;324&rarr;334&rarr;330&rarr;340&rarr;300&rarr;310&rarr;320&rarr;321&rarr;331&rarr;341&rarr;
> 301&rarr;311&rarr;312&rarr;322&rarr;332&rarr;342&rarr;302&rarr;303&rarr;313&rarr;323&rarr;333&rarr;343&rarr;
> 443&rarr;444&rarr;440&rarr;441&rarr;401&rarr;402&rarr;403&rarr;404&rarr;400&rarr;410&rarr;411&rarr;412&rarr;413&rarr;
> 414&rarr;424&rarr;420&rarr;421&rarr;422&rarr;423&rarr;433&rarr;434&rarr;430&rarr;431&rarr;432&rarr;442&rarr;042.

Triples for the same value of s are spaced exactly m steps apart. To prove that all m<sup>3</sup> triples occur, we need
to prove that the m<sup>2</sup> triples for any given value of s are all present.

Notice that the first coordinate, i, changes only when s = 0 and j = m&minus;1. Thus the m<sup>2</sup> triples with
any given value of the first coordinate i all occur consecutively. (Our example cycles indicate this by starting
at the vertex where i has just changed to 0, instead of starting at vertex 000.)

Notice that the cycle elements with i = 0 must start in general with the vertex 0(m&minus;1)2, because the
previous vertex must have had i = j = m&minus;1 and s = 0. And 0(m&minus;1)2, which has s = 1, is followed in
general by 002, 012, ..., 0(m&minus;3)2, 0(m&minus;3)3, taking us back to s = 0.

In general 0(m&minus;k)k is immediately followed by 0(m&minus;k)(k+1) when 1 < k < m; and then j increases
until we reach 0(m&minus;k&minus;2)(k+1), whose successor is 0(m&minus;k&minus;2)(k+2). Thus k is increased by 2, modulo m,
each time we hit a vertex with s = 0. Since m is odd, we'll eventually get to 0(m&minus;1)1 --- at which time we
will have seen all m<sup>2</sup> vertices of the form 0jk. And the successor of 0(m&minus;1)1 is 1(m&minus;1)1.

So far so good! In general, the cycle elements whose first component i satisfies 0 < i < m&minus;1 will start
with i(m&minus;1)(2&minus;i), where 2&minus;i is of course evaluated mod m. If all goes well those elements should include
all m<sup>2</sup> vertices that begin with i, ending with i(m&minus;i)(1&minus;i) --- whose successor is (i+1)(m&minus;1)(1&minus;i). And
all does go well: We repeatedly advance the second component except when s = 0; hence the vertices that
we see when s = 0 are i(m&minus;2)(2&minus;i), i(m&minus;3)(3&minus;i), ..., i&middot;0(m&minus;i), i(m&minus;1)(1&minus;i).

Finally we reach (m&minus;1)(m&minus;1)3, the first vertex for which i = m&minus;1. The local rules change again:
From now on we'll repeatedly advance the third component, except when s = m&minus;1. The vertices we see
when s = 0 are (m&minus;1)01, (m&minus;1)10, ..., (m&minus;1)(m&minus;1)2. QED.

We've now proved that the first cycle (the cycle for c = 0 in the C program) is Hamiltonian. Similar
proofs can be carried out for the other two cycles. (See the Appendix.)

For fun, let's consider a larger class of cycles for which such proofs exist. Indeed, it turns out that there
are hundreds of way to solve the stated decomposition problem for odd m; Claude Opus 4.6 happened to
discover just one of them, by deducing where to look.

We shall say that a Hamiltonian cycle C for m = 3 is *generalizable* if the following construction yields
a Hamiltonian cycle for all odd m &ge; 3: "Given an arbitrary vertex IJK for 0 &le; I, J, K < m, let i = I', j = J', s = S', and k = (s&minus;i&minus;j) mod 3, where S = (I+J+K) mod m, 0' = 0, (m&minus;1)' = 2, and x' = 1 for
0 < x < m&minus;1. Obtain the successor of IJK by bumping the coordinate that cycle C bumps when forming
the successor of ijk." For example, if m = 5 and IJK = 301, we have i = 1, j = 0, S = 4, s = 2, k = 1. So
the successor of 301 will be either 401 or 311 or 302, depending on whether C contains the arc 101 &rarr; 201
or 101 &rarr; 111 or 101 &rarr; 102.

Claude's cycle in the example above for m = 3 is generalizable; indeed, we've seen its generalization for
m = 5. But it's easy to find cycles that are *not* generalizable. For instance, if C is the cycle

> 000&rarr;001&rarr;002&rarr;012&rarr;010&rarr;011&rarr;021&rarr;022&rarr;020&rarr;120&rarr;100&rarr;101&rarr;111&rarr;121&rarr;
> 122&rarr;102&rarr;112&rarr;110&rarr;210&rarr;211&rarr;212&rarr;222&rarr;220&rarr;221&rarr;201&rarr;202&rarr;200&rarr;000

(which happens to be the lexicographically smallest of all Hamiltonian cycles for the case m = 3), we get
the following "generalization" for m = 5:

> 000&rarr;001&rarr;002&rarr;003&rarr;004&rarr;014&rarr;010&rarr;011&rarr;012&rarr;013&rarr;023&rarr;024&rarr;020&rarr;
> 021&rarr;022&rarr;032&rarr;033&rarr;034&rarr;030&rarr;031&rarr;041&rarr;042&rarr;043&rarr;044&rarr;040&rarr;140&rarr;
> 100&rarr;101&rarr;102&rarr;103&rarr;113&rarr;123&rarr;124&rarr;120&rarr;121&rarr;221&rarr;231&rarr;232&rarr;233&rarr;
> 234&rarr;334&rarr;344&rarr;340&rarr;341&rarr;342&rarr;302&rarr;312&rarr;313&rarr;314&rarr;310&rarr;410&rarr;411&rarr;
> 412&rarr;413&rarr;414&rarr;424&rarr;420&rarr;421&rarr;422&rarr;423&rarr;433&rarr;434&rarr;430&rarr;431&rarr;432&rarr;
> 442&rarr;443&rarr;444&rarr;440&rarr;441&rarr;401&rarr;402&rarr;403&rarr;404&rarr;400&rarr;000.

Oops --- this cycle has length 75, not 125.

It turns out that there are exactly 11502 Hamiltonian cycles for m = 3, of which exactly 1012 generalize
to Hamiltonian cycles for m = 5. Furthermore, exactly 996 of them generalize to Hamiltonian cycles for
both m = 5 and m = 7. And those 996 are in fact generalizable to all odd m > 1.

Now here's the point: Let's say that a decomposition is "Claude-like" if it can be generated by a C
program like the one above, in which the permutations d of {0, 1, 2} depend only on whether i, j, and s are
0 or m&minus;1 or not. No special cases other than 0 and m&minus;1 are allowed to affect the choice of d.

**Theorem.** *A Claude-like decomposition is valid for all odd m > 1 if and only if each of the three sequences
that it defines for m = 3 is generalizable.*

*Proof.* If those three sequences aren't Hamiltonian, or if they don't generalize to Hamiltonian cycles for all
odd m > 1, they certainly don't define a valid decomposition. Conversely, if they are Hamiltonian cycles
that generalize to Hamiltonian cycles for all odd m > 1, they certainly are valid: Every vertex ijk appears in
each of the three cycles, and its three outgoing arcs are partitioned properly because d is a permutation. &#x25A0;

By setting up an exact cover problem, using the 11502 Hamiltonian cycles for m = 3, we can deduce
that there are exactly 4554 solutions to the 3&times;3&times;3 decomposition problem. And in a similar fashion, if we
study all ways to cover every arc by using just three of the 996 cycles that are generalizable, we find that
exactly 760 of those 4554 solutions involve only generalizable cycles --- about one in every 6. Consequently
the theorem tells us that exactly 760 Claude-like decompositions are valid for all odd m > 1.

Maybe the decomposition that Claude found wasn't the "nicest" of those 760. Can we do better? I
looked at several of them and found that they have somewhat different behaviors. Yet I didn't encounter
any that were actually nicer.

The dependence on i, j, and s means that these decompositions don't have cyclic symmetry. I did
notice, to my surprise, that 136 of the 760 generalizable 3&times;3&times;3 cycles remain generalizable when we map
ijk to jki. However, none are common to all three mappings {ijk, jki, kij}.

Filip told me that the explorations reported above, though ultimately successful, weren't really smooth.
He had to do some restarts when Claude stopped on random errors; then some of the previous search results
were lost. After every two or three test programs were run, he had to remind Claude again and again that
it was supposed to document its progress carefully.

Delicious success for odd m, at exploration number 31, came about one hour after the session began.

This decomposition problem remains open for even values of m. The case m = 2 was proved impossible
long ago [1]. As part of exploration number 24, Claude said that it had found solutions for m = 4, m = 6,
and m = 8; yet it saw no way to generalize those results.

Filip also told me that he asked Claude to continue on the even case after the odd case had been resolved.
"But there after a while it seemed to get stuck. In the end, it was not even able to write and run explore
programs correctly anymore, very weird. So I stopped the search."

All in all, however, this was definitely an impressive success story. I think Claude Shannon's spirit is
probably proud to know that his name is now being associated with such advances. Hats off to Claude!

## Appendix

Claude's second cycle (c = 1) is governed by the following rules: "If s = 0, bump j.
If 0 < s < m+1, bump i. If s = m&minus;1 and i > 0, bump k. If s = m&minus;1 and i = 0, bump j."

TRANSCRIPTION NOTE: the m+1 above should likely be m&minus;1, but for now we faithfully transcribe the pdf.

We can show that the vertices with s = 0 are seen in the following order, for k = 0, 1, ..., m&minus;1:
0&middot;k(&minus;k), (&minus;2)(1+k)(1&minus;k), (&minus;4)(2+k)(2&minus;k), ..., 2(&minus;1+k)(&minus;1&minus;k). And that will establish the order in
which vertices with s = 1, 2, ..., m&minus;1 are seen.

Claude's third cycle (c = 2) is governed by somewhat more complex rules: "If s = 0 and j < m&minus;1,
bump i. If s = 0 and j = m&minus;1, bump k. If 0 < s < m&minus;1 and i < m&minus;1, bump k. If 0 < s < m&minus;1 and
i = m&minus;1, bump j. If s = m&minus;1, bump i."

The vertices with s = 0 and j < m&minus;1 are seen in the following order: 0&middot;j(&minus;j), 2&middot;j(&minus;2&minus;j), 4&middot;j(&minus;4&minus;j), ...,
(&minus;2)j(2&minus;j). And the successors of the latter vertex are (&minus;1)j(2&minus;j), (&minus;1)(j+1)(2&minus;j), (&minus;1)(j+2)(2&minus;j),
..., (&minus;1)(j&minus;2)(2&minus;j), 0(j&minus;2)(2&minus;j).

But the vertices with s = 0 and j = m&minus;1 are seen thus: 0(&minus;1)1, 1(&minus;1)0, 2(&minus;1)(&minus;1), ..., (&minus;1)(&minus;1)2.
And the successors of the latter vertex are (&minus;1)(&minus;1)3, (&minus;1)03, (&minus;1)13, ..., (&minus;1)(&minus;3)3, 0(&minus;3)3.

Thus in every case the sequence of m vertices for s = 0 and a given j is followed by the sequence for
s = 0 and j&minus;2, modulo m.

## Postscript

On March 3, Stappers wrote me as follows: "The story has a bit of a sequel. I put Claude
Opus 4.6 to work on the m = even cases again for about 4 hours yesterday. It made some progress, but not
a full solution. The final program ... sets up a partial fiber construction similar to the odd case, then runs
a search to fix it all up. ... Claude spent the last part of the process mostly on making the search quicker
instead of looking for an actual construction. ... It was running many programs trying to find solutions
using simulated annealing or backtrack. After I suggested to use the ORTools CP-SAT [part of Google's open
source toolkit, with the AddCircuit constraint] to find solutions, progress was better, since now solutions
could be found within seconds." This program is [4].

Then on March 4, another friend --- Ho Boon Suan in Singapore --- wrote as follows: "I have code
generated by gpt-5.3-codex that generates a decomposition for even m &ge; 8.
... I've tested it for all
even m from 8 to 200 and bunch of random even values between 400 and 2000, and it looks good. Seems far
more chaotic to prove correctness by hand here though; the pattern is way more complex." That program
is [5]. (Wow. The graph for m = 2000 has 8 billion vertices!)

## References

[1] Jacques Aubert and Bernadette Schneider, "Graphes orient&eacute;s ind&eacute;composables en circuits hamiltoniens."
*Journal of Combinatorial Theory* B32 (1982), 347--349.

[2] Donald E. Knuth, *The Art of Computer Programming, Volume 4A: Combinatorial Algorithms, Part 1*
(Upper Saddle River, N. J.: Addison--Wesley, 2011), xvi+883 pp.

[3] Donald E. Knuth, preliminary drafts entitled "Hamiltonian paths and cycles," currently posted at
https://cs.stanford.edu/~knuth/fasc8a.ps.gz and updated frequently as more material is being accumulated.

[4] https://cs.stanford.edu/~knuth/even_solution.py

[5] https://cs.stanford.edu/~knuth/even_closed_form.c
