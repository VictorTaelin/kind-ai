Kind-AI
=======
For some time, I have been discussing the hypothetical integration of AI with proof languages like Kind, and how this would result in the greatest increase in programmer efficiency in history. I am writing this Gist to elaborate on this idea. The basic concept is simple:

  1. You use dependent types to write a precise specification of the program you need.
  2. GPT (the AI) thinks about your specification and then writes a program for you.
  3. GPT is asked to prove that its implementation is correct.
  4. If it is incorrect, it is asked to determine what is wrong and fix it.
  5. If it is correct, the result is shown to the programmer.

The crucial step here is step 3. This is where GPT typically fails, in verifying the correctness of its output. This is also the main reason why we can't ask GPT to build large software, as errors will accumulate and prevent all parts from fitting together to form a working project that compiles. But there is a solution to this problem: a proof checker. With its help, we can identify incorrect output and ask GPT to fix it, in an automated back-and-forth process that will ultimately result in the correct program. By repeating this process enough times, we can generate arbitrarily large, correct software automatically from a prompt -- and I don't think I need to explain how revolutionary that would be. To fully understand the idea, you first need to understand what a formal proof is.

What is a formal proof?
-----------------------

For the purpose of this document, we can consider a proof to be an argument that asserts that a given program meets some specification. For instance, let's say we want to implement a function that negates a Boolean value. We could start with a type:

```
Not (x: Bool) : Bool
```

This is beneficial because it prevents us from creating "obviously incorrect" functions, such as one that returns strings or numbers, which would result in a type error. However, it does not prevent us from writing incorrect programs. For example, the code below passes the type checker, even though it is incorrect:

```
// Very wrong, yet it DOES type-check!
Not (x: Bool) : Bool
Not x = match x {
  true  => true
  false => false
}
```

The issue is that the type systems in most programming languages are not expressive enough to encode arbitrary specifications. On dependently typed languages like Kind, we can write the following type:

```
Spec (x: Bool) : Not (Equal Bool (Func x) x)
```

Here, we use dependent types to specify that the input of Func must be different from its output. In other words, the existence of Spec makes it impossible to write Not in a way that does not negate its input, which would result in a static type error.

But how does the type checker verify that a specification is satisfied? One approach could be to perform a brute-force search, testing all inputs to ensure none of them violate the specification, but that would obviously not be feasible for functions with an infinite domain. Instead, a dependent type checker requires a logical proof that the specification is valid. To give you an idea of what such a proof would look like, here is the proof that Not is correct after we fix it:

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

Don't worry about understanding it. Just note that this proof contains all the information necessary for the compiler to verify that the specification is satisfied. And that's the essence of proofs. In short, they provide us with two new powerful tools:

  1. A language for specifying arbitrarily complex program specifications
  2. A verifier capable of checking, given a proof, that the specification is satisfied

That's all you need to know.

How can formal proofs guide AI?
-------------------------------

Now that you understand what a formal proof is, its role in AI will become clearer. Recently, we have seen the emergence of AI tools that generate programs automatically. For example, if you provide GPT-3 with the following prompt:

```
Write a JavaScript function named "not" that takes in a boolean and returns its negation. Do not use the "!" or "?" operators.
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

Which is perfectly correct! But if we request something more **specific**, like:

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

Which is incorrect... sometimes. For the string `"foo X bar"` it outputs `"X"`, which is correct. But for the string `"foo XX Y bar"`, it also outputs `"X"`, which is incorrect, as the correct answer would be `"Y"`. This program is simple enough for most developers to spot the issue, but it's not feasible for larger programs. Additionally, since these small errors accumulate, it is virtually impossible for GPT to produce large software in one go.

However, despite this, GPT is still very good at making great guesses for small program fragments. If we had an external tool that could break down big problems into smaller problems and evaluate whether a specific guess is correct, then GPT would be able to create large software that works. That's why I believe integrating formal proofs with a LLM (Language Model) would be so powerful.

A complete example (PoC)
------------------------

Let's test this hypothesis with a small proof-of-concept by integrating Kind's type checker with GPT and asking it to write the program **correctly**. To do this, let's start by replacing the **English prompt** with a **typed specification**.

```
Func (str: Stream Char) : Nat
Spec0 (str: Stream Char) : Equal (Stream.at str (Nat.pred (Func str))) ' '
Spec1 (str: Stream Char) : Equal (Stream.at str (Nat.succ (Func str))) ' '
```

This specification states that `Func` is a `Stream Char -> Nat` function, meaning it takes in a sequence of characters and returns a number. However, this doesn't provide much information about what `Func` does. The specifications, on the other hand, specify that for a given output of `Func str`, the elements before and after that index must be spaces. Therefore, the only way for `Func` to pass the type checker is if it returns the index of an element surrounded by spaces, which is what we require. This not only gives the AI the necessary information to determine the function it needs to build, but it also allows the AI to prove that its output is correct.

Now, let's test the hypothesis by having GPT implement Func by using the idea discussed at the beginning of this gist. Please note that all prompts used will be generic, avoiding any clues or strong direction given to GPT. However, I will sometimes ask it to focus more, explain its reasoning, or identify its own mistakes. The goal is to show that these prompts could be automated, although not as directly as I will demonstrate here, but consistently and progressively.

We start by educating GPT about Kind, and then we ask it to consider what `Func` must be, based on the types of `Spec0` and `Spec1`.

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
This is a really good guess, but it's incorrect. In the first clause, Spec1 is not being upheld, as GPT never checks if the second character is a space. **That's why this setup is so effective: given this proposed implementation, GPT would never be able to prove that `Spec0` and `Spec1` are correct**. As a result, the algorithm would prompt GPT for a proof, which it wouldn't be able to provide. Eventually, it would give up. When that happens, the algorithm would go back to the proposed solution, inform GPT that it is probably incorrect, and ask why. Keep in mind that it would have information on the failed proof attempts to assist. In this case, we simply say that it's wrong and ask GPT to determine why:

```
The implementation above seems to be wrong. That means that one or more of the
equations do not respect some of the specifications. Which equation does not
satisfy which spec? Why?
```

Even though it has no additional information, it realizes its mistake:

```
The equation `Func (Stream.cons c (Stream.cons ' ' str)) = Nat.succ (Func
(Stream.cons c str))` does not satisfy Spec0 because the predecessor of Nat.succ
(Func (Stream.cons c str)) is not necessarily a space character. It could be any
character, depending on the value of c.
```

I then proceed to ask it to rethink what it must do:

```
What must be true about the output of an equation for both specs to be satisfied?
```

GPT answers correctly:

```
The output of an equation must be a Nat such that the character at the Nat's
predecessor and successor in the Stream are both space characters.
```

I then ask it to try another solution.

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

Even though it still gets the RHS wrong, this back-and-forth debate between the proof checker, the prompts, and the AI will accumulate information on what the function must do, what mistakes must be avoided, and so on. Eventually, a correct implementation of `Func` will be proposed.

```
Func (str: Stream Char) : Nat
Func (Stream.cons ' ' (Stream.cons c (Stream.cons ' ' str))) = Nat.succ Nat.zero
Func (Stream.cons c str)                                     = Nat.succ (Func str)
```
It may take some time, but once the implementation of Func is correct, GPT will be able to complete the proof in a way that satisfies the type checker. This process may be different, but to get started, we'll begin the prompt with the proposed solution and ask GPT to consider it. This will assist it in the upcoming theorem-proving process.

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
This is not 100% correct, but it is almost on target. For the actual proof, I believe that an interactive game where, at each step, the AI proposes a tactic to advance, would work best. Let's give it a try.

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
This is not only the correct move, but it is also a correct proof sketch. This approach is compelling because most conventional proof search techniques would waste a lot of time searching through an exponential number of unproductive branches, but GPT was able to guide us in the right direction on the first try. That's remarkable. Let's proceed by giving it the updated state.

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
That's correct, and it completes the proof for this case! Let's give it the other:

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
That's once again the right move, and directly completes the proof. Soon enough, GPT is able to produce the following program and proofs:

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

By integrating GPT with a proof checker (Kind) and a series of prompts that can be generated automatically, it appears that we can create arbitrarily complex programs and get correct outputs. In this exercise, we started by writing a specification:

```
// Func is a function from char streams to Nat
Func (str: Stream Char) : Nat

// The character before the index returned by Func must be a space
Spec0 (str: Stream Char) : Equal (Stream.at str (Nat.pred (Func str))) ' '

// The character after the index returned by Func must be a space
Spec1 (str: Stream Char) : Equal (Stream.at str (Nat.succ (Func str))) ' '
```

Given that specification, the integration of GPT and Kind would internally perform a series of queries that would result in the generation of the following program: 

```
Func (str: Stream Char) : Nat
Func (Stream.cons ' ' (Stream.cons c (Stream.cons ' ' str))) = Nat.succ Nat.zero
Func (Stream.cons c str)                                     = Nat.succ (Func str)
```

With the caveat that the program is only presented to the developer once the AI has successfully proved that it works. In other words, the programmer does not need to check the generated code for correctness. This hypothetical scenario would allow programmers to work in a completely different manner: they would simply write specifications in the form of precise types and let the AI write the programs for them. We could even go a step further and generate specifications from English prompts, leading to amazing applications. For instance, imagine you could write a prompt like:

> write a Pokémon MMORPG with Genshin Impact like open world and Valorant like PVP

You then wait for some time and are handed a complete, working directory containing all the necessary files to host and play your game world. All components from the server to the client to the sprite generators were generated behind the scenes by breaking down the prompt into smaller sub-components, converting them into Kind types, and applying the algorithm to fill each type in a way that works, so that they can be assembled piece by piece into the full project.

While this exercise is obviously very rough, and I had to intervene in some parts by insisting on specific ideas or asking GPT to reconsider its answer, I did very little, if any, actual coding beyond writing the specification. GPT hasn't been fine-tuned for this kind of application, but once it is, I believe that the whole process could become automated. Furthermore, the process generates a new program/proof pair that can be included in the database and used to further train the AI, enabling it to get better and better at writing programs. With enough time, this loop may cause the AI to create an entire field of mathematical theorems and proofs beyond our comprehension, making any human proof seem like a piece of cake.

Disclaimer
----------

While this is new to me, I am aware that the field of automatic theorem proving has existed for a long time, and it is very likely that everything that I wrote here has already been considered and/or is being done currently. I would love to meet people who are working on this sort of stuff, because I truly believe that this is the most important thing humanity should be investing in right now. Here is a relevant link:

- https://arxiv.org/pdf/2210.11610.pdf

- https://gowers.wordpress.com/2022/04/28/announcing-an-automatic-theorem-proving-project/

- Templates: [prompt #0](https://platform.openai.com/playground/p/aZnyl9aT4GpshqfHEAtmKXDv), [prompt #1](https://platform.openai.com/playground/p/NfYCnMFjWBWMdOiCTP0J6X0g)
