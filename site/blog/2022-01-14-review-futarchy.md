---
layout: post
title: "Review: Shall We Vote on Values, But Bet on Beliefs?"
date: 2022-01-14 15:55
comments: true
tags: review, hanson, futarchy, economics, mechanism design
---

Another week, another paper review. This week we're looking at Robin Hanson's
["Shall We Vote on Values, But Bet on Beliefs?"][futarchy] (SWVVBBB). In
SWVVBBB, Hanson proposes a new form of government he calls "futuarchy," which
injects prediction markets into democratic government.

[futarchy]:

The preamble starts like this:

1. Democracies fail by not aggregating information
2. Prediction markets are really good at aggregating information
3. We can postdict which nations did better than others.

These three assumptions seem relatively self-evident, though perhaps the first
is the least obvious. In support of this assumption, Hanson presents some
evidence:

1. Most people vote the same way they've always voted.
2. Most people don't know what the government is doing.
3. Most people don't know which platforms parties stand for.
4. It's hard for governments to disseminate information.
5. The populace often has different ideas about what government should do than
   what experts say it should do.
6. At large, the populace believes in a bunch of rather crazy things (eg. 85% of
   Americans believe Jesus was born to a virgin, and 52% believe astrology has
   some scientific proof.)
7. It seems untenable that bad policy decisions would be adopted if they were
   known to be bad policy decisions.

The first three points are pretty easy to believe as well. The fourth is also
tenable; the government relies on mainstream media to get messages out, where it
can be editorialized before being published. Points five and six taken together
suggest that the people are often *wrong* about what constitutes good policy.

Hanson presents sources for these claims, but I don't have any issues taking
them on faith --- this isn't the crux of the paper. It's safe to say that
failure to aggregate information is a serious problem in democracies.

Why does this matter? Because democracy gives us one vote, with which not only
do we need to vote on our values, but also on how we'd like the government to
bring about those values. For example, political parties' platforms involve both
*values* ("we care about healthcare, equality, housing, etc."), and *strategy*
("we will build 1,000,000 new houses and hire 50,000 new nurses.")

Personally, I support Canada's left-most party's values, but I don't think
they'd be very capable if they actually got into power. This tension leads me
away from voting for them, in an attempt to find a better mix of *competent* and
*represents what I care about.*

The question that SWVVBBB answers is "how can we separate voting for values from
voting for execution of those values." And as the title suggests, the trick is
to do it by putting our money where our mouths are.


## Betting on Beliefs

The main contribution of SWVVBBB in my opinion is its clever mechanism design to
pull *probabilities* out of *prices.* This will take some explanation.

At a high level, the idea is we should vote for a party based only on our
values. The winning party is responsible for choosing an explicit mathematical
function that represents how well the country is doing on its values. For
example, this function might be "GDP", or "percent of the population employed,"
or "global happiness ranking," or what have you. Probably, it will be some
combination of these things.

The government's only job is to define what success looks like, and how we're
going to measure it. That's all the government does. They don't get to raise
taxes, or allocate spending, or appoint judges, or anything like that. They are
responsible only to pick the utility function, and to create any agencies that
might be required to measure it.

Here's where it gets interesting.

We now put a prediction market in place. For a fee, anybody can propose any
intervention on the way the country is run. Collectively, people buy and sell
bonds corresponding to whether they think the proposal will help maximize the
government's value function. By looking at the market price of the bonds, we can
get a good sense of whether or not the market thinks the proposal is a good
idea. If it is, the proposal immediately gets turned into law.

The details on how to actually go about building this market are a good chunk of
the paper, which we will get to in the next section. For now, let's continue
thinking about the high-level idea.

By connecting the law to a market, we immediately get a few benefits. The first
is that we now incentivize people to have true beliefs about governance. If my
ideas about how the country should be run are in fact good, I can make money off
of that skill. Furthermore, it incentivizes transparency. If people can make
lots of money off of this market, you can bet they'll watch it extremely
closely.

Perhaps best of all, it pushes stupid people out of the market. If you are
consistently *wrong* about what constitutes good governance, you will quickly
price yourself out of the market --- similar to people who go broke trying to
play the stock market on the advice of their uncle.

To be clear, this doesn't disenfranchise people. They still get to vote on the
government. But it requires questions of policy to be answered by putting your
money where your mouth is. Thus, under this scheme, it becomes prohibitively
expensive to have stupid beliefs strongly held.


## Mechanism Design

So, that's the high level idea. How do we actually go about implementing it?


### Discovering Probability

Imagine a particular question of fact, that can be definitely observed in the
future. For example, maybe we want to determine whether or not it will be
raining next Friday at 10am in the park beside my house. The more specific the
question, the better.

The bank can offer a pair of assets:

1. Pays \\\$1 if it is raining on Friday at 10am.
2. Pays \\\$1 if it is not raining on Friday at 10am.

and the bank is happy to sell these assets for \\\$1, because exactly one of them
will actually pay off. In the meantime, the bank can collect interest for free.

Suppose Market-Making Marty buys 10,000 of these pairs from the bank. Marty can
now sell the assets individually, for example, he might sell some not raining
assets to Dusty, and some raining assets to Misty. Initially, he might price
both assets at \\\$0.60.

By selling both sides of the pair at \\\$0.60, Marty safely makes \\\$2,000 dollars
off of his \\\$10,000 investment. It's safe because he no longer holds any assets
except for cold hard cash.

Dusty figures that it's sunny more than 60% of the time, so paying \\\$0.60 for an
asset that pays \\\$1.00 is a good deal. If he estimates the likelihood of it being
sunny on Friday at 80%, then he expects an 80% chance of making \\\$10,000, and a
20% chance of making \\\$0. Adding these together, he computes his expected value
at $0.8 * 10000 + 0.2 * 0 = 8000$, which is \\\$2,000 more in expectation than the
cost of buying all the assets at \\\$6,000.

Misty does some chain of reasoning that makes her believe that her money is also
well spent.

Summer has been thinking hard, and is pretty sure the chance of rain on Friday
is actually closer to 5%. So she approaches Dusty, and offers to buy some of his
no-rain assets for \\\$0.90. Dusty thinks this is too confident, so he happily
unloads his options to Summer, since again he expects to be making money on this
trade.

When everything settles, no-rain assets are trading at a market price of \\\$0.83,
while rain assets are at \\\$0.17 (in the limit, these must add up to \\\$1.00, or
else you can make money by holding both sides.)

Patty, who was thinking about having a picnic in the park on Friday, looks at
the asset prices, and decides it's not going to rain, since no-rain is trading
above rain.

Thus, Patty has made a decision about the future, based on information
aggregated from Dusty, Misty, Summer, and whoever else might have been in on the
market.

Friday comes along, and it doesn't rain. Patty is happy, as is everyone holding
no-rain assets, since they all made money.


### Discovering Expected Value

We can play the same game to extract information about expected values from the
market. Suppose we want to guess the price of flour next week. The bank can look
at the historical high of flour price, and sell pairs of assets:

1. Pays \\\$x, where `x` is the percentage of the cost of flour with respect to
   its all-time high. For example, if the all-time high was \\\$40, and the cost
   of flour next week was \\\$30, this asset pays \\\$0.75 ($30/40$).
2. Pays \\\$(1 - x).

Again, the bank is happy to make this trade because they are still only paying
out \\\$1, and they still get to make interest on that dollar until the market pays
out.

The trading price of these assets now correspond to the market's opinion of the
expected value of the price of flour next week. If \\\$x assets are trading at
\\\$0.30, we can read the expected value of flour next week to be $0.3 * 40 = 12$.


### Conditional Assets

There's one last trick we can do. We can make conditional assets, that is,
assets which only pay out when a certain precondition is met. We can consider
the case of whether or not a big law firm BLF wins its case, conditional on
whether or not they put Litigious Larry on as the lead prosecutor. In this case,
the bank offers quads of assets for \\\$1:

1. Pays \\\$1 if BLF wins with Larry
2. Pays \\\$1 if BLF wins without Larry
3. Pays \\\$1 if BLF loses with Larry
4. Pays \\\$1 if BLF loses without Larry

Again, only one of these four cases will actually pay out (ignoring the
possibility that it doesn't go to court, but that's a simplification for the
example, not a limitation of the technique.)

Like Patty in the park, BLF can make a decision about the future: whether or not
they should put Larry on the case based on whether Win|Larry is trading higher
than Win|-Larry.

Furthermore, they can rethink whether or not they want to settle out of court if
the BLF loses assets are trading at better than BLF wins.


## Putting It Into Practice

With the mechanism design under our belt, we can now think about implementing
futarchy.

The people vote on the government based on parties' values. The government puts
forward its value function. Now, anyone can pay a transaction fee (perhaps quite
high) to propose a policy intervention. The bank can offer a pair of assets:

1. Pays \\\$x if the intervention is made
2. Pays \\\$(1-x) if the intervention is made

where x is linear in the observed value function at some point in the future.
The idea is to tie the payoff of the asset to how well it helps influence our
value function.

For example, maybe the government decides the value function is GDP. Maybe the
target GDP in five years is \\\$30 trillion. Phoebe then proposes building a
high-speed train between Toronto and Vancouver. The bank can offer assets as
above, where x is the observed percentage of GDP out of \\\$30 trillion.

After some period of trading, the \\\$x assets are trading well above \\\$(1-x). This
is interpreted as the market thinking this train would be good for long term
GDP. Immediately, the decision to build the train is ensconced in law.

That doesn't mean all the details are necessarily worked out. If Phoebe had the
whole plan for the train worked out, she could have put those in her proposal.
But let's assume she didn't. Instead, someone can make a new proposal, that
Cost-Cutting Carlos should get put in charge of the project. At the same time,
there is a proposal that Safety Susan should be put in charge. Markets pop up
for both, and whichever is trading higher gets the bid (unless neither is
trading well!)

We can follow this process ad infinitum, to work out more and more particulars.
If, at any time, someone thinks the train is actually a bad idea, they can make
a proposal to stop its development. We need not worry about the inefficiency
inherent this sort of flip-flopping; the market will necessarily price-in the
sunk costs.

