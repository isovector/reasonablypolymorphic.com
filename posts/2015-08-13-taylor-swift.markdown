---
layout: post
title: Encasing Taylor Swift
date: 2015-08-13 11:29
comments: true
tags: math, fun
---

I'm not much of a reddit guy, but I just found a neat one:
[r/theydidthemath][math]. Here's the gist: people ask silly questions, and other
people looking to do some mathematical recreation answer their silly questions.

[math]: https://www.reddit.com/r/theydidthemath/

[Here's one][taylor] that tickled my fancy:

[taylor]: https://www.reddit.com/r/theydidthemath/comments/3gsos3/request_if_you_took_the_net_worth_of_taylor_swift/

> If you took the net worth of Taylor Swift, in &#36;20 bills, and used those as
> building blocks, how big of an enclosure could you build around her and still
> have it remain soundproof?

Great question. Let's see if we can figure it out.

A [quick google search][netwo] indicates that Taylor Swift's net worth is
&#36;240 million USD. WolframAlpha, the source of all sorts of fantastic and
weird mathematical facts, [states][bill] the volume of a &#36;20 USD bill is
$1138 \text{mm}^3$, which gives us an easy $2.4\cdot 10^8 \text{USD} \times 1138
\text{mm}^3\text{/ USD} = 2731 \text{m}^3$ of building material to work with.

[netwo]: https://www.google.com/search?q=net%20worth%20of%20taylor%20swift
[bill]: http://www.wolframalpha.com/input/?i=volume+of+a+%2420+USD+bill

Good start.

We will assume an enclosure around Taylor Swift is a hemisphere shell, and for
good measure, we'll pad the floor of the enclosure as well. The volume of a
hemisphere is

$$
v = \frac{4 \pi \left(r_o^3 - r_i^3\right)}{6}
$$

where $r_o$ and $r_i$ are the outer and inner radii of the sphere, respectively.
Since sound attenuates over distance, it would be more helpful to describe $r_i$
as the attenuation distance (which is to say, the necessary thickness of our
shell). We rewrite the hemisphere's volume as:

$$
v = \frac{4 \pi \left(r^3 - (r-s)^3\right)}{6}
$$

where $s$ is now the shell thickness, and $r$ is the outer radius.

To this, we'll add a cylinder of radius $r_i = r - s$ and height $s$ to pad the
floor. The total volume of our enclosure solid is thus:

$$
v = \frac{4 \pi \left(r^3 - (r-s)^3\right)}{6} + \pi s (r - s)^2
$$

I don't know much about sound attenuation, but according to [atten][this page],
sound dissipates according to the law:

[atten]: https://www.nde-ed.org/EducationResources/CommunityCollege/Ultrasonics/Physics/attenuation.htm

$$
A = A_0 e^{-\alpha x}
$$

where $A_0$ is the initial loudness, $A$ is the resulting loudness,  $\alpha$ is
the attenuation coefficient of the material, and $x$ is the distance the
sound travels through the material.

The initial question doesn't state if we're trying to sound-proof Taylor Swift
or *a Taylor Swift concert*, so let's try doing both. [Regular human
speech][loudn] is $A_0 = 60 \text{dB}$, and a rock concert (we're being generous,
here) is approximately $A_0 = 115 \text{dB}$. We assume dampening the sound down to
the loudness of a whisper is acceptable, so this gives us $A = 30 \text{dB}$.

[loudn]: http://www.gcaudio.com/resources/howtos/loudness.html

Solving our attenuation for $x$ (which is $s$, the necessary width of our shell
to achieve sound dampening), we get:

$$
s = \frac{\ln{A_0}-\ln{A}}{\alpha}
$$

Great! So given $\alpha$, we should be able to compute $s$. Strangely, there
doesn't seem to be much in the literature for the sound attenuation coefficient
for paper, so we'll have to use an educated guess here. [This page][coeff] gives
coefficients for a few common engineering materials, the closest to paper of
which is probably cork.

[coeff]: http://www.engineeringtoolbox.com/accoustic-sound-absorption-d_68.html

If you were going to *actually build* this enclosure around poor Taylor, you
would probably want to experimentally find a value for this (and have some
*really* good lawyers), but we'll assume
cork is close enough to paper to continue our analysis.

Substituting in $\alpha = 0.15$, the mean coefficient listed for cork, we get:

$$
s_t = \frac{\ln{60}-\ln{30}}{0.15} = 4.6 \text{m}  \\\\
s_c = \frac{\ln{115}-\ln{30}}{0.15} = 9.0 \text{m} \\\\
$$

where $s_t$ is the necessary shell width to silence Taylor Swift, and $s_c$, to
silence her concert.

Because doing math is hard, we'll use WolframAlpha [to do the remaining
calculations for us][answer]:

[answer]: http://www.wolframalpha.com/input/?i=solve+%282731+%3D+%284+*+pi+*+%28r%5E3+-+%28r-s%29%5E3%29%29%2F6+%2B+2+*+pi+*+s+*+%28r+-+s%29%5E2+with+s+%3D+4.6%29+for+r

$$
r_t = 10.9 \text{m} \\\\
r_c = 10.8 \text{m}
$$

This is a little surprising, that the maximum size of our enclosure for a
sound-proofed concert would be larger than the enclosure to silence Taylor
Swift, and this might be an artifact of letting computers do our math for us.

There is another interpretation, however: this is the *outer* radius of the
enclosure. In the concert case, the outer radius is $r_c = 10.8 \text{m}$, but
the shell is $s_c = 9.0 \text{m}$ thick, which means the living space on the
inside is about a measly $10 \text{m^2}$. This sonuds not terrible, until you
remember it's inside of a dome -- which excludes a lot of your living space from
area you can do things with.

But it's definitely not enough room to play a concert.

