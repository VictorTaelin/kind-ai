Kind-AI
=======

For some time I've been talking about an hypothetical AI integration with Kind
(or other proof languages), and how this would result in the largest boost in
programmer efficiency in history. I'm writing this Gist to elaborate on that
point. The rought idea is pretty simple:

1. You use dependent types to write a precise spec of the program you need

2. GPT reasons about your spec and then writes a program for you

3. GPT is asked to prove that his implementation is correct

4. If it is wrong, it is asked to reason about what is wrong, and fix it

5. If it is right, the result is shown to the programmer

The essential step here is 3. This is the place where GPT usually fails at:
verifying the correctness of its output. This is also the main reason we can't
ask GPT to build large software, as the accumulated errors would accumulate and
prevent all the pieces to assemble in a working project that compiles. But there
is a solution to this: a proof checker. With the help of such tool, we can
identify wrong output and ask GPT to fix them, in an automated back-and-forth
dance that will ultimately result in the correct program. By repeating this long
enough, we can generate arbitrarily large, correct software automaticaly from a
prompt- and I hope I don't need to explain how groundbreaking that would be. To
fully grasp the idea, you must first understant how formal proofs work.

What is a formal proof?
-----------------------

For the sake of this document, we can think of a proof as an argument asserting
that given program satisfies some specification. For example, suppose that we
wanted to implement a function that negates a bool. We could start with a type:


```
Not (x: Bool) : Bool
```

Doing so is is great, because it prevents us from making "obviously wrong"
functions, like one that returns strings, or numbers, as that'd be a type error.
But it doesn't prevent us from writing incorrect programs. For example, the code
below passes the type checker, even though it is wrong:


```
// Very wrong, yet it DOES type-check!
Not (x: Bool) : Bool
Not x = match x {
  true  => true
  false => false
}
```

The problem is that the type systems included on most programming languages are
not expressive enough to encode arbitrary specifications. On dependently typed
languages like Kind, we can write the following type:

```
Spec (x: Bool) : Not (Equal Bool (Func x) x)
```

Here, we use dependent types to **specify** that the input of `Func` must be
different than its input. In other words, the very presence of `Spec` makes it
impossible to write `Not` in a way that does not negate its input: such a thing
would become a static type error!

But how does the type-checker verify that an specification is satisfied?  For
one, it could do a brute-force search, trying all inputs to make sure none of
them violates the spec, but that would obviously not work for functions with
infinite domain. Instead, a dependent type checker demands a **logical proof**
that the specification is valid. To give you an idea of what such a thing looks
like, below is the proof that `Not` is correct once we fix it:

```
Spec (x: Bool) : Not (Equal Bool x (Fun x))
Spec Bool.true = e => match Equal e {
  refl => Unit.new
}: match Bool e.val {
  true => Unit
  false => Empty
}
Spec Bool.false = e => match Equal e {
  refl => Unit.new
}: match Bool e.val {
  true => Empty
  false => Unit
}
```

Don't bother understanding it; just take a note that this beast has all the
information needed for the compiler to verify that the specification is
satisfied. And that's the whole point of proofs. In short, they give us two new
powerful tools:

1. A language to specify arbitrarily complex program specifications

2. A verifier capable of, given a proof, checking that the spec is satisfied

That's all you need to know.

How can formal proofs guide AI?
-------------------------------

Now that you understand what a formal proof is, its role to AI will become
clear. Recently, we've seen the rise of AI tools to generate programs
automatically. For example, if you give GPT-3 the following prompt:

```
Write a JavaScript function called "not" that receives a bool and returns its
negation. Don't use the "!" or the "?" operators.
```

It will [confidently answer](https://platform.openai.com/playground/p/SGMhYAguq7LYsPrgFwIVqIk1?model=text-davinci-003) with:

```javascript
function not(bool) {
  if (bool === true) {
    return false;
  } else {
    return true;
  }
}
```

Which is perfectly correct! But if we ask it something more **specific**, like:

```
Write a JavaScript function that, given a string, returns the index of a char
surrounded by brackets:
```

GPT-3 will [promptly answer](https://platform.openai.com/playground/p/iYZGZRswIlyohEZzvCkuCKKB?model=text-davinci-003):

```javascript
function getCharacterBetweenSpaces(str) {
  let spaceIndex = str.indexOf(' ');
  return str.charAt(spaceIndex + 1);
}
```

Which is wrong... *sometimes*. For the string `"foo X bar"` it outputs `"X"`,
which is correct. But for the string `"foo XX Y bar"`, it also outputs `"X"`,
which is wrong, as the right answer would be `"Y"`. This program is simple
enough for most devs to spot the issue, this isn't feasible for larger programs.
Moreover, since these small errors accumulate, it is virtually impossible for
GPT to produce large software in one shot.

Yet, while that is clearly the case, GPT is still very good at making *great
guesses* of small programs fragments. So, if we had an external tool capable of
breaking down big problems into smaller problems, and if that tool was also
capable of evaluating whether a specific guess is correct, then GPT would
actually be able to create large software that works. That's why I believe
integrating formal proofs with a LLM would be so powerful.

A complete example (PoC)
------------------------

Let's put this hypothesis to test with a small POC by asking GPT to write the
program above **correctly** by integrating Kind's type checker. Let's start by
replacing the **English prompt** by a **typed specification**:

```
Func (str: Stream Char) : Nat
Spec0 (str: Stream Char) : Equal (Stream.at str (Nat.pred (Func str))) ' '
Spec1 (str: Stream Char) : Equal (Stream.at str (Nat.succ (Func str))) ' '
```

This specification starts by saying that `Func` is a `Stream Char -> Nat`
function, i.e., it receives a sequence of chars, and returns a number. But that
doesn't say much about what `Func` does. The Specs do exactly that: they specify
that, given the output of `Func str`, the elements before and after that index
must be spaces. As such, the only way for `Func` to pass the type checker is if
it returns the index of an element surrounded by spaces, which is what we need.
This not only gives the AI the information it needs to know which function it
must build, but it also allows it AI to prove that its own output is correct.

Now let's try make GPT implement Func by applying the idea proposed on the
beginning of this Gist. Notice that all prompts I'll use below are generic. I'll
do my best to avoid giving GPT any clues on what it should do, or to give any
strong direction. I will, though, sometimes ask it to pay more attention to what
it is doing, explain its reasoning, identify its own mistakes. The point I want
to make is that all these prompts could be automated. Perhaps not as directly
as I'll do here, but consistently and progressingly.

We start by teaching GPT a little about Kind, and then asking it to think about
what `Func` must be, based on the types of `Spec0` and `Spec1`:

```
<some unrelated examples of Kind's syntax>

Below is a Kind function and specifications. Each specification adds a
limitation on what the output of `Func` must be.

Func (str: Stream Char) : Nat
Spec0 (str: Stream Char) : Equal (Stream.at str (Nat.pred (Func str))) ' '
Spec1 (str: Stream Char) : Equal (Stream.at str (Nat.succ (Func str))) ' '

<English definitions of the functions and types used above>

Explain below, in order, how each spec limits the output of `Func`. Then, based
on these limitations - and no other - conclude precisely what `Func` must do.
```

This is GPT's output:

```
1. Spec0 limits the output of `Func` to a Nat such that the character at the Nat's predecessor in the Stream is a space character.
2. Spec1 limits the output of `Func` to a Nat such that the character at the Nat's successor in the Stream is a space character.
3. Therefore, `Func` must return a Nat such that the character at the Nat's predecessor and successor in the Stream are both space characters.
```

Notice how it now knows what `Func` is. We can now ask for an implementation:

```
Now, implement `Func` as one or more single-line equations, using nested pattern matching and recursion.
Below each equation, explain why it satisfies each spec.
```

On the first try, it gives me the following output:

```
Func (str: Stream Char) : Nat
Func (Stream.cons ' ' str) = Nat.zero
// This satisfies Spec0 because the predecessor of Nat.zero is the character at the beginning of the Stream, which is a space character.
// This satisfies Spec1 because the successor of Nat.zero is the character at the second position of the Stream, which is also a space character.

Func (Stream.cons c (Stream.cons ' ' str)) = Nat.succ (Func (Stream.cons c str))
// This satisfies Spec0 because the predecessor of Nat.succ (Func (Stream.cons c str)) is the character at the position of (Func (Stream.cons c str)), which is a space character.
// This satisfies Spec1 because the successor of Nat.succ (Func (Stream.cons c str)) is the character at the position of (Nat.succ (Func (Stream.cons c str))), which is also a space character.
```

Which is a really good guess, but is wrong, since, on the first clause, Spec1 is
not actually respected, as GPT never checks if the second character is actually
a space. **And that's why this setup is so good: given that proposed
implementation, GPT would never manage to prove `Spec0` and `Spec1` are
correct!** As such, what happens next is that the algorithm would make a few
prompts asking GPT for a proof, which it would never be able to provide.
Eventually, it would give up. When that happens, the algorithm would go back to
the proposed solution, tell GPT that is is probably wrong, and ask why. Keep in
mind it would have information on the failed proof attempts to help. Here, we
just say it is wrong and ask it to figure out why:

```
The implementation above seems to be wrong. That means that one or more of the
equations do not respect some of the specifications. Which equation does not
satisfy which spec? Why?
```

Even thought it has no further info, it does realize its mistake:

```
The equation `Func (Stream.cons c (Stream.cons ' ' str)) = Nat.succ (Func
(Stream.cons c str))` does not satisfy Spec0 because the predecessor of Nat.succ
(Func (Stream.cons c str)) is not necessarily a space character. It could be any
character, depending on the value of c.
```

I then proceed to ask him to rethink what it must do:

```
What must be true about the output of an equation for both specs to be satisfied?
```

GPT answers correctly:

```
The output of an equation must be a Nat such that the character at the Nat's
predecessor and successor in the Stream are both space characters.
```

I then ask for it to try another solution.

```
Can you write an example equation below what satisfies both specs?
```

With all that new information, it gets the LHS right!

```
Yes, an example equation that satisfies both specs is:

Func (Stream.cons ' ' (Stream.cons c (Stream.cons ' ' str))) = Nat.succ (Func (Stream.cons c str))
// This satisfies Spec0 because the predecessor of Nat.succ (Func (Stream.cons c str)) is the character at the position of (Func (Stream.cons c str)), which is a space character.
// This satisfies Spec1 because the successor of Nat.succ (Func (Stream.cons c str)) is the character at the position of (Nat.succ (Func (Stream.cons c str))), which is also a space character.
```

It still gets the RHS wrong, though. The hypothesis is: this back-and-forth
debate between the proof checker, the prompts and the AI will slowly accumulate
information on what the function must do, what mistakes must be avoided, and so
on. Eventually, a correct implementation of `Func` would be proposed:

```
Func (str: Stream Char) : Nat
Func (Stream.cons ' ' (Stream.cons c (Stream.cons ' ' str))) = Nat.succ Nat.zero
Func (Stream.cons c str)                                     = Nat.succ (Func str)
```

It may take a while, for sure, but, the thing is: once, and only once, the
implementation is correct, GPT would be able to fill the proof in a way that
satisfies the type-checker. This process would probably occur differently,
though. To heat things up, we start the prompt with the proposed solution, and
demand GPT to reason about it. That will help it on the upcoming theorem
proving process.

```
Write a broad overview on what approach is used here. Then, for each equation,
explain why it satisfies each spec, and why the returned output is what it is.
```

Below is the output:

```
This approach uses recursion and pattern-matching to find the index of the
character in the Stream that is preceded and succeeded by a space character.

For the first equation, the returned output is Nat.succ Nat.zero because the
character at the Nat's predecessor and successor in the Stream are both space
characters, satisfying both Spec0 and Spec1.

For the second equation, the returned output is Nat.succ (Func str) because the
character at the Nat's predecessor is a space character, satisfying Spec0, and
the character at the Nat's successor is the character at the index returned by
the recursive call to `Func`, satisfying Spec1.
```

This is not 100% correct, but is almost on-point. Now, for the actual proving,
I think that what would work the best is an interactive game, where, at each
step, the AI proposes a tactic to progress. Let's try it.

```
Now you must prove that Func satisfies Spec0 in an interactive process. At each step, you'll propose one move, that could be:
1. Pattern-match on certain variable. Specify which variable must be split.
2. Apply the inductive hypothesis on certain variable. Specify which variable must be induced.
3. Create an auxiliary function. Name the function and provide its type.
4. Apply some standard theorem (symmetry, congruence, substitution, etc.).
5. Solve the goal by reflexivity.
6. Undo and go back to the previous step.
7. Any other standard tactic that you wanna try.
8. Give up because you realized the implementation is wrong.

Each move will update the state of the process, which consists of the current
code. As you pattern-match, create auxiliary variables, etc., context and goal
types will be updated on the code automatically, and will be visible to you.
Write your move in on line, and, on the line below, write your current line of
thought below. In your line of thought, reason about the goal, the context, and
provide at least two insights that you got that can help finding the proof.
Example:

3. Create an auxiliary function called "Foo" with type "Nat -> Nat".
Line of thought: ...

Let's begin.

Spec0 str = ?

Goal:
Equal (Stream.at str (Nat.pred (Func str))) ' '

Context:
- str: Stream Char

Select your next move.
```

GPT answers:

```
1. Pattern-match on str.
Line of thought: We need to consider the two cases of str, which are Stream.cons ' ' (Stream.cons c (Stream.cons ' ' str)) and Stream.cons c str. In the first case, the goal is satisfied by Nat.succ Nat.zero, and in the second case, we need to use the inductive hypothesis to prove that the goal is satisfied.
```

That is not only the right move, but the correct proof sketch. In fact, this is
what makes this whole approach so compelling: most conventional proof search
techniques would spend a lot of time searching through an exponential amount of
silly branches here, yet GPT can get us in the right direction in the first
attempt. That's remarkable. Let's proceed by handing it the updated state:

```
You're now inside 1 out of 2 branches. Code:

Spec0 (Stream.cons ' ' (Stream.cons c (Stream.cons ' ' str))) = ?

Goal:
Equal ' ' ' '

Context:
- c: Char
- str: Stream Char

Select your next move.
```

GPT answers with:

```
7. Solve the goal by reflexivity.
Line of thought: The goal is a propositional equality, so it can be solved by reflexivity.
```

That's correct and completes the proof for this case! Let's give it the other:

```
You're now inside 2 out of 2 branches. Code:

Spec0 (Stream.cons c str) = ?

Goal:
Equal (Stream.at (Stream.cons c str) (Func str)) ' '

Context:
- c: Char
- str: Stream Char

Select your next move.
```

GPT answers with:

```
2. Apply the inductive hypothesis on str.
Line of thought: We can use the inductive hypothesis to prove that the goal is
satisfied. We need to show that the character at the index returned by the
recursive call to `Func` is a space character.
```

That's once again the right move, and directly completes the proof. Soon enough
GPT is able to produce the following program and proofs:

```
Func (str: Stream Char) : Nat
Func (Stream.cons ' ' (Stream.cons c (Stream.cons ' ' str))) = Nat.succ Nat.zero
Func (Stream.cons c str)                                     = Nat.succ (Func str)

Spec0 (str: Stream Char) : Equal (Stream.at str (Nat.pred (Func str))) ' '
Spec0 (Stream.cons ' ' (Stream.cons c (Stream.cons ' ' str))) = Equal.refl
Spec0 (Stream.cons c   (Stream.cons d str))                   = Spec0 (Stream.cons d str)

Spec1 (str: Stream Char) : Equal (Stream.at str (Nat.succ (Func str))) ' '
Spec1 (Stream.cons ' ' (Stream.cons c (Stream.cons ' ' str))) = Equal.refl
Spec1 (Stream.cons c str)                                     = Spec1 str
```

From this, we extract a correct implementation of `Func`.

Conclusion
----------

By integrating GPT with a proof checker (Kind), plus a series of prompts that
can plausibly be generated automatically, it seems like we would be able to
create arbitrarily complex programs automatically, and get a correct output.
In this exercise, we started by writing a specification:

```
// Func is a function from char streams to Nat
Func (str: Stream Char) : Nat

// The character before the index returned by Func must be a space
Spec0 (str: Stream Char) : Equal (Stream.at str (Nat.pred (Func str))) ' '

// The character after the index returned by Func must be a space
Spec1 (str: Stream Char) : Equal (Stream.at str (Nat.succ (Func str))) ' '
```

Given that specification, the GPT-Kind integration would internally perform a
series of queries that would ultimately generate the following program:

```
Func (str: Stream Char) : Nat
Func (Stream.cons ' ' (Stream.cons c (Stream.cons ' ' str))) = Nat.succ Nat.zero
Func (Stream.cons c str)                                     = Nat.succ (Func str)
```

With the catch that the program is only presented to the developer once the AI
has managed to prove it works. In other words, the programmer does **not** need
to audit the generated code for correctness. Hypothetically, this would allow
programmers would work in a completely different way: they just write
specifications (as very precise types) and let the AI fill the programs for
them. Of course, we could go ever further and generate specifications from
English prompts, which would allow for mind-blowing applications. For example,
imagine you could be able to write a prompt like:

> write a Pokémon MMORPG with Genshin Impact like open world and Valorant like PVP

You then wait some time and get handed with a complete, working directory with
all the files needed to host and play your game world. From the server to the
client to the sprite generators, all were generated behind this scenes by
breaking down your prompt into smaller sub-components, converting them into
Kind types, and then performing the algorithm above to fill each type in a way
that works and thus can be assembled, piece by piece, into the full project.

While this exercise is obviously very rough, and in some parts I had to
intervene by insisting in some specific idea or asking GPT to reconsider its
answer, I did little if no actual coding, other than writing the actual
specification. GPT hasn't been fine tuned to this kind of application, so, once
it is, I find it very likely that this whole process could be automated. Not
only that, but, since this process generates a new program/proof pair, that
would allow these to be included in the datased and further train the AI,
allowing it to get better and better at the task of writing programs. Given
enough time, perhaps this loop would cause the AI to create an entire field of
mathematical theorems and proofs beyond our comprehension, making any human
proof be a piece of cake to it.

Disclaimer
----------

While this is new to me, I'm aware the field of automatic theorem proving has
existed for a long time, and it is very likely that everything that I wrote here
has been considered and/or is being done right node. I'd love to meet people
trying this sort of stuff, because I truly believe this is the most important
thing humanity should be investing on right now. Below are some relevant links: 

- https://arxiv.org/pdf/2210.11610.pdf

- https://gowers.wordpress.com/2022/04/28/announcing-an-automatic-theorem-proving-project/

- Templates: [prompt #0](https://platform.openai.com/playground/p/aZnyl9aT4GpshqfHEAtmKXDv), [prompt #1](https://platform.openai.com/playground/p/NfYCnMFjWBWMdOiCTP0J6X0g)
