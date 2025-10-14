---
layout: post
title: Arrows to Arrows, Categories to Queries
date: 2025-10-14 14:31
comments: true
tags: haskell, category theory, programming, catlang
---

I've had a little time off of work as of late, and been spending it in
characteristically unwise ways. In particular, I've written a [little
programming language that compiles to
SQL](https://github.com/isovector/catlang). I call it *catlang*. That's not to
say that I've written a new query language. It's a programming language, whose
compiler spits out one giant `SELECT` statement. When you run that query in
postgres, you get the output of your program.

Why have I done this? Because I needed a funny compilation target to test out
the actual features of the language, which is that its intermediary language is
a bunch of abstract category theory nonsense. Which I'll get to. But I'm sure
you first want to see this bad boy in action.

Behold, the function that returns 100 regardless of what input you give it. But
it does it with the equivalent of a while loop:

```haskell
count : Int -> Int
count =
  x ->
    loop x
      i ->
        n <- join id id -< i
        z <- abs . (-) -< (n, 100)
        case z of
          inl _ -> inr . (+) -< (n, 1)
          inr _ -> inl -< n
```

If you're familiar with [arrow notation](/blog/arrowized-frp/), you'll notice
the above looks kinda like one big `proc` block. This is not a coincidence
(because nothing is a coincidence). I figured if I were to go through all of
this work, we might as well get a working arrow desugarer out of the mix. But I
digress; that's a story for another time.

Anyway, what's going on here is we have an arrow `count`, which takes a single
argument `x`. We then loop, starting from the value of `x`. Inside the loop, we
now have a new variable `i`, which we do some voodoo on to compute `n`---the
current value of the loop variable. Then we subtract 100 from `n`, and take the
absolute value. The `abs` function here is a bit odd; it returns `Left (abs x)`
if the input was negative, and `Right x` otherwise. Then we branch on the output
of `abs`, where `Left` and `Right` have been renamed `inl` and `inr`
respectively. If `n - 100` was less than zero, we find ourselves in the `inl`
case, where we add 1 to `n` and wrap the whole thing in `inr`---which the loop
interprets as "loop again with this new value." Otherwise, `n - 100` was
non-negative, and so we can return `n` directly.

Is it roundabout? You bet! The obtuseness here is not directly a feature, I was
just looking for conceptually simple things I could do which would be easy to
desugar into category-theoretical stuff. Which brings us to the intermediary
language. After desugaring the source syntax for `count`
above, we're left with this IL representation:

```
  id △ id
⨟ cochoice
    ( undist
    ⨟   ( (prj₁ ⨟ id ▽ id) △ id
          ⨟   ( prj₁ △ 100
              ⨟ (-)
              ⨟ abs
              )
            △ id
          ⨟ prj₁ △ id
          ⨟ dist
          ⨟   ( (prj₂ ⨟ prj₂ ⨟ prj₁) △ 1
              ⨟ (+)
              ⨟ inr
              )
            ▽ ( prj₂
              ⨟ prj₂
              ⨟ prj₁
              ⨟ inl
              )
        )
      △ prj₂
    ⨟ dist
    )
⨟ prj₁
```

We'll discuss all of this momentarily, but for now, just let your eyes
glaze over the pretty unicode.

The underlying idea here is that each of these remaining symbols has very simple
and specific algebraic semantics. For example, `A ⨟ B` means "do `A` and pipe
the result into `B`." By giving a transformation from this categorical IL
into other domains, it becomes trivial to compile catlang to all sorts of
weird compilation targets. Like SQL.

You're probably wondering what the generated SQL looks like. Take a peek if you
dare.

<details>
<summary>Ungodly Compiled SQL</summary>

```sql
SELECT
f0 AS f0
FROM
(SELECT
 f0 AS f0, f1 AS f1
 FROM
 (SELECT *
  FROM
  (WITH t0 AS
   (SELECT *
    FROM
    (WITH RECURSIVE recursion AS
     (SELECT
      clock_timestamp() as step
      , *
      FROM
      (WITH t1 AS
       (SELECT *
        FROM
        (SELECT
         f0 AS f0, f1 AS f1, NULL::integer AS f2, NULL::integer AS f3
         FROM
         (WITH t2 AS
          (SELECT * FROM (SELECT 0 as f0) AS _)
          SELECT *
          FROM
          (SELECT * FROM (SELECT f0 AS f0 FROM t2 AS _) AS _
           CROSS JOIN
           (SELECT f0 AS f1 FROM t2 AS _))
          AS _)
         AS _)
        AS _)
       SELECT *
       FROM
       (WITH t3 AS
        (SELECT *
         FROM
         (-- undist
          SELECT *
          FROM
          (SELECT
           f0 AS f0, NULL::integer AS f1, f1 AS f2
           FROM
           (-- undist1
            SELECT * FROM t1 AS _ WHERE "f0" IS NOT NULL)
           AS _)
          AS _
          UNION
          SELECT *
          FROM
          (SELECT
           NULL::integer AS f0, f2 AS f1, f3 AS f2
           FROM
           (-- dist2
            SELECT * FROM t1 AS _ WHERE "f2" IS NOT NULL)
           AS _)
          AS _)
         AS _)
        SELECT *
        FROM
        (WITH t4 AS
         (SELECT *
          FROM
          (SELECT *
           FROM
           (SELECT
            f0 AS f0, f1 AS f1
            FROM
            (WITH t5 AS
             (SELECT * FROM t3 AS _)
             SELECT *
             FROM
             (WITH t6 AS
              (SELECT *
               FROM
               (SELECT *
                FROM
                (SELECT
                 f0 AS f0
                 FROM
                 (WITH t7 AS
                  (SELECT * FROM (SELECT f0 AS f0, f1 AS f1 FROM t5 AS _) AS _)
                  SELECT *
                  FROM
                  (SELECT *
                   FROM
                   (SELECT
                    f0 AS f0
                    FROM
                    (-- join1
                     SELECT * FROM t7 AS _ WHERE "f0" IS NOT NULL)
                    AS _)
                   AS _
                   UNION
                   SELECT *
                   FROM
                   (SELECT
                    f1 AS f0
                    FROM
                    (-- join2
                     SELECT * FROM t7 AS _ WHERE "f1" IS NOT NULL)
                    AS _)
                   AS _)
                  AS _)
                 AS _)
                AS _
                CROSS JOIN
                (SELECT f0 AS f1, f1 AS f2, f2 AS f3 FROM t5 AS _))
               AS _)
              SELECT *
              FROM
              (WITH t8 AS
               (SELECT *
                FROM
                (SELECT *
                 FROM
                 (SELECT
                  f0 AS f0, f1 AS f1
                  FROM
                  (WITH t9 AS
                   (SELECT *
                    FROM
                    (SELECT
                     f0 - f1 AS f0
                     FROM
                     (WITH t10 AS
                      (SELECT * FROM t6 AS _)
                      SELECT *
                      FROM
                      (SELECT *
                       FROM
                       (SELECT f0 AS f0 FROM (SELECT f0 AS f0 FROM t10 AS _) AS _)
                       AS _
                       CROSS JOIN
                       (SELECT f0 AS f1 FROM (SELECT 100 as f0 FROM t10 AS _) AS _))
                      AS _)
                     AS _)
                    AS _)
                   SELECT *
                   FROM
                   (SELECT *
                    FROM
                    (SELECT
                     abs(f0) as f0, NULL::integer as f1
                     FROM
                     t9
                     AS _
                     WHERE
                     f0 < 0)
                    AS _
                    UNION
                    SELECT *
                    FROM
                    (SELECT NULL::integer as f0, f0 as f1 FROM t9 AS _ WHERE f0 >= 0)
                    AS _)
                   AS _)
                  AS _)
                 AS _
                 CROSS JOIN
                 (SELECT f0 AS f2, f1 AS f3, f2 AS f4, f3 AS f5 FROM t6 AS _))
                AS _)
               SELECT *
               FROM
               (WITH t11 AS
                (SELECT *
                 FROM
                 (SELECT *
                  FROM
                  (SELECT
                   f0 AS f0, f1 AS f1
                   FROM
                   (SELECT f0 AS f0, f1 AS f1 FROM t8 AS _)
                   AS _)
                  AS _
                  CROSS JOIN
                  (SELECT
                   f0 AS f2, f1 AS f3, f2 AS f4, f3 AS f5, f4 AS f6, f5 AS f7
                   FROM
                   t8
                   AS _))
                 AS _)
                SELECT *
                FROM
                (WITH t12 AS
                 (SELECT *
                  FROM
                  (-- dist
                   SELECT *
                   FROM
                   (SELECT
                    f0 AS f0, f2 AS f1, NULL::integer AS f10, NULL::integer AS f11, NULL::integer AS f12, NULL::integer AS f13, f3 AS f2, f4 AS f3, f5 AS f4, f6 AS f5, f7 AS f6, NULL::integer AS f7, NULL::integer AS f8, NULL::integer AS f9
                    FROM
                    (-- dist1
                     SELECT * FROM t11 AS _ WHERE "f0" IS NOT NULL)
                    AS _)
                   AS _
                   UNION
                   SELECT *
                   FROM
                   (SELECT
                    NULL::integer AS f0, NULL::integer AS f1, f4 AS f10, f5 AS f11, f6 AS f12, f7 AS f13, NULL::integer AS f2, NULL::integer AS f3, NULL::integer AS f4, NULL::integer AS f5, NULL::integer AS f6, f1 AS f7, f2 AS f8, f3 AS f9
                    FROM
                    (-- dist2
                     SELECT * FROM t11 AS _ WHERE "f1" IS NOT NULL)
                    AS _)
                   AS _)
                  AS _)
                 SELECT *
                 FROM
                 (SELECT *
                  FROM
                  (SELECT
                   NULL::integer AS f0, f0 AS f1
                   FROM
                   (SELECT
                    f0 + f1 AS f0
                    FROM
                    (WITH t13 AS
                     (SELECT *
                      FROM
                      (SELECT
                       f0 AS f0, f1 AS f1, f2 AS f2, f3 AS f3, f4 AS f4, f5 AS f5, f6 AS f6
                       FROM
                       (-- join1
                        SELECT * FROM t12 AS _
                        WHERE
                        ("f0" IS NOT NULL) AND ((("f1" IS NOT NULL) OR ("f2" IS NOT NULL)) AND (("f3" IS NOT NULL) AND ((("f4" IS NOT NULL) OR ("f5" IS NOT NULL)) AND ("f6" IS NOT NULL)))))
                       AS _)
                      AS _)
                     SELECT *
                     FROM
                     (SELECT *
                      FROM
                      (SELECT
                       f0 AS f0
                       FROM
                       (SELECT
                        f0 AS f0
                        FROM
                        (SELECT
                         f2 AS f0, f3 AS f1, f4 AS f2, f5 AS f3
                         FROM
                         (SELECT
                          f1 AS f0, f2 AS f1, f3 AS f2, f4 AS f3, f5 AS f4, f6 AS f5
                          FROM
                          t13
                          AS _)
                         AS _)
                        AS _)
                       AS _)
                      AS _
                      CROSS JOIN
                      (SELECT f0 AS f1 FROM (SELECT 1 as f0 FROM t13 AS _) AS _))
                     AS _)
                    AS _)
                   AS _)
                  AS _
                  UNION
                  SELECT *
                  FROM
                  (SELECT
                   f0 AS f0, NULL::integer AS f1
                   FROM
                   (SELECT
                    f0 AS f0
                    FROM
                    (SELECT
                     f2 AS f0, f3 AS f1, f4 AS f2, f5 AS f3
                     FROM
                     (SELECT
                      f1 AS f0, f2 AS f1, f3 AS f2, f4 AS f3, f5 AS f4, f6 AS f5
                      FROM
                      (SELECT
                       f7 AS f0, f8 AS f1, f9 AS f2, f10 AS f3, f11 AS f4, f12 AS f5, f13 AS f6
                       FROM
                       (-- join2
                        SELECT * FROM t12 AS _
                        WHERE
                        ("f7" IS NOT NULL) AND ((("f8" IS NOT NULL) OR ("f9" IS NOT NULL)) AND (("f10" IS NOT NULL) AND ((("f11" IS NOT NULL) OR ("f12" IS NOT NULL)) AND ("f13" IS NOT NULL)))))
                       AS _)
                      AS _)
                     AS _)
                    AS _)
                   AS _)
                  AS _)
                 AS _)
                AS _)
               AS _)
              AS _)
             AS _)
            AS _)
           AS _
           CROSS JOIN
           (SELECT f0 AS f2 FROM (SELECT f2 AS f0 FROM t3 AS _) AS _))
          AS _)
         SELECT *
         FROM
         (-- dist
          SELECT *
          FROM
          (SELECT
           f0 AS f0, f2 AS f1, NULL::integer AS f2, NULL::integer AS f3
           FROM
           (-- dist1
            SELECT * FROM t4 AS _ WHERE "f0" IS NOT NULL)
           AS _)
          AS _
          UNION
          SELECT *
          FROM
          (SELECT
           NULL::integer AS f0, NULL::integer AS f1, f1 AS f2, f2 AS f3
           FROM
           (-- dist2
            SELECT * FROM t4 AS _ WHERE "f1" IS NOT NULL)
           AS _)
          AS _)
         AS _)
        AS _)
       AS _)
      AS _
      UNION ALL
      SELECT
      clock_timestamp() as step
      , *
      FROM
      (SELECT *
       FROM
       (WITH t14 AS
        (SELECT * FROM recursion AS _)
        SELECT *
        FROM
        (WITH t15 AS
         (SELECT *
          FROM
          (-- undist
           SELECT *
           FROM
           (SELECT
            f0 AS f0, NULL::integer AS f1, f1 AS f2
            FROM
            (-- undist1
             SELECT * FROM t14 AS _ WHERE "f0" IS NOT NULL)
            AS _)
           AS _
           UNION
           SELECT *
           FROM
           (SELECT
            NULL::integer AS f0, f2 AS f1, f3 AS f2
            FROM
            (-- dist2
             SELECT * FROM t14 AS _ WHERE "f2" IS NOT NULL)
            AS _)
           AS _)
          AS _)
         SELECT *
         FROM
         (WITH t16 AS
          (SELECT *
           FROM
           (SELECT *
            FROM
            (SELECT
             f0 AS f0, f1 AS f1
             FROM
             (WITH t17 AS
              (SELECT * FROM t15 AS _)
              SELECT *
              FROM
              (WITH t18 AS
               (SELECT *
                FROM
                (SELECT *
                 FROM
                 (SELECT
                  f0 AS f0
                  FROM
                  (WITH t19 AS
                   (SELECT * FROM (SELECT f0 AS f0, f1 AS f1 FROM t17 AS _) AS _)
                   SELECT *
                   FROM
                   (SELECT *
                    FROM
                    (SELECT
                     f0 AS f0
                     FROM
                     (-- join1
                      SELECT * FROM t19 AS _ WHERE "f0" IS NOT NULL)
                     AS _)
                    AS _
                    UNION
                    SELECT *
                    FROM
                    (SELECT
                     f1 AS f0
                     FROM
                     (-- join2
                      SELECT * FROM t19 AS _ WHERE "f1" IS NOT NULL)
                     AS _)
                    AS _)
                   AS _)
                  AS _)
                 AS _
                 CROSS JOIN
                 (SELECT f0 AS f1, f1 AS f2, f2 AS f3 FROM t17 AS _))
                AS _)
               SELECT *
               FROM
               (WITH t20 AS
                (SELECT *
                 FROM
                 (SELECT *
                  FROM
                  (SELECT
                   f0 AS f0, f1 AS f1
                   FROM
                   (WITH t21 AS
                    (SELECT *
                     FROM
                     (SELECT
                      f0 - f1 AS f0
                      FROM
                      (WITH t22 AS
                       (SELECT * FROM t18 AS _)
                       SELECT *
                       FROM
                       (SELECT *
                        FROM
                        (SELECT f0 AS f0 FROM (SELECT f0 AS f0 FROM t22 AS _) AS _)
                        AS _
                        CROSS JOIN
                        (SELECT f0 AS f1 FROM (SELECT 100 as f0 FROM t22 AS _) AS _))
                       AS _)
                      AS _)
                     AS _)
                    SELECT *
                    FROM
                    (SELECT *
                     FROM
                     (SELECT
                      abs(f0) as f0, NULL::integer as f1
                      FROM
                      t21
                      AS _
                      WHERE
                      f0 < 0)
                     AS _
                     UNION
                     SELECT *
                     FROM
                     (SELECT NULL::integer as f0, f0 as f1 FROM t21 AS _ WHERE f0 >= 0)
                     AS _)
                    AS _)
                   AS _)
                  AS _
                  CROSS JOIN
                  (SELECT f0 AS f2, f1 AS f3, f2 AS f4, f3 AS f5 FROM t18 AS _))
                 AS _)
                SELECT *
                FROM
                (WITH t23 AS
                 (SELECT *
                  FROM
                  (SELECT *
                   FROM
                   (SELECT
                    f0 AS f0, f1 AS f1
                    FROM
                    (SELECT f0 AS f0, f1 AS f1 FROM t20 AS _)
                    AS _)
                   AS _
                   CROSS JOIN
                   (SELECT
                    f0 AS f2, f1 AS f3, f2 AS f4, f3 AS f5, f4 AS f6, f5 AS f7
                    FROM
                    t20
                    AS _))
                  AS _)
                 SELECT *
                 FROM
                 (WITH t24 AS
                  (SELECT *
                   FROM
                   (-- dist
                    SELECT *
                    FROM
                    (SELECT
                     f0 AS f0, f2 AS f1, NULL::integer AS f10, NULL::integer AS f11, NULL::integer AS f12, NULL::integer AS f13, f3 AS f2, f4 AS f3, f5 AS f4, f6 AS f5, f7 AS f6, NULL::integer AS f7, NULL::integer AS f8, NULL::integer AS f9
                     FROM
                     (-- dist1
                      SELECT * FROM t23 AS _ WHERE "f0" IS NOT NULL)
                     AS _)
                    AS _
                    UNION
                    SELECT *
                    FROM
                    (SELECT
                     NULL::integer AS f0, NULL::integer AS f1, f4 AS f10, f5 AS f11, f6 AS f12, f7 AS f13, NULL::integer AS f2, NULL::integer AS f3, NULL::integer AS f4, NULL::integer AS f5, NULL::integer AS f6, f1 AS f7, f2 AS f8, f3 AS f9
                     FROM
                     (-- dist2
                      SELECT * FROM t23 AS _ WHERE "f1" IS NOT NULL)
                     AS _)
                    AS _)
                   AS _)
                  SELECT *
                  FROM
                  (SELECT *
                   FROM
                   (SELECT
                    NULL::integer AS f0, f0 AS f1
                    FROM
                    (SELECT
                     f0 + f1 AS f0
                     FROM
                     (WITH t25 AS
                      (SELECT *
                       FROM
                       (SELECT
                        f0 AS f0, f1 AS f1, f2 AS f2, f3 AS f3, f4 AS f4, f5 AS f5, f6 AS f6
                        FROM
                        (-- join1
                         SELECT * FROM t24 AS _
                         WHERE
                         ("f0" IS NOT NULL) AND ((("f1" IS NOT NULL) OR ("f2" IS NOT NULL)) AND (("f3" IS NOT NULL) AND ((("f4" IS NOT NULL) OR ("f5" IS NOT NULL)) AND ("f6" IS NOT NULL)))))
                        AS _)
                       AS _)
                      SELECT *
                      FROM
                      (SELECT *
                       FROM
                       (SELECT
                        f0 AS f0
                        FROM
                        (SELECT
                         f0 AS f0
                         FROM
                         (SELECT
                          f2 AS f0, f3 AS f1, f4 AS f2, f5 AS f3
                          FROM
                          (SELECT
                           f1 AS f0, f2 AS f1, f3 AS f2, f4 AS f3, f5 AS f4, f6 AS f5
                           FROM
                           t25
                           AS _)
                          AS _)
                         AS _)
                        AS _)
                       AS _
                       CROSS JOIN
                       (SELECT f0 AS f1 FROM (SELECT 1 as f0 FROM t25 AS _) AS _))
                      AS _)
                     AS _)
                    AS _)
                   AS _
                   UNION
                   SELECT *
                   FROM
                   (SELECT
                    f0 AS f0, NULL::integer AS f1
                    FROM
                    (SELECT
                     f0 AS f0
                     FROM
                     (SELECT
                      f2 AS f0, f3 AS f1, f4 AS f2, f5 AS f3
                      FROM
                      (SELECT
                       f1 AS f0, f2 AS f1, f3 AS f2, f4 AS f3, f5 AS f4, f6 AS f5
                       FROM
                       (SELECT
                        f7 AS f0, f8 AS f1, f9 AS f2, f10 AS f3, f11 AS f4, f12 AS f5, f13 AS f6
                        FROM
                        (-- join2
                         SELECT * FROM t24 AS _
                         WHERE
                         ("f7" IS NOT NULL) AND ((("f8" IS NOT NULL) OR ("f9" IS NOT NULL)) AND (("f10" IS NOT NULL) AND ((("f11" IS NOT NULL) OR ("f12" IS NOT NULL)) AND ("f13" IS NOT NULL)))))
                        AS _)
                       AS _)
                      AS _)
                     AS _)
                    AS _)
                   AS _)
                  AS _)
                 AS _)
                AS _)
               AS _)
              AS _)
             AS _)
            AS _
            CROSS JOIN
            (SELECT f0 AS f2 FROM (SELECT f2 AS f0 FROM t15 AS _) AS _))
           AS _)
          SELECT *
          FROM
          (-- dist
           SELECT *
           FROM
           (SELECT
            f0 AS f0, f2 AS f1, NULL::integer AS f2, NULL::integer AS f3
            FROM
            (-- dist1
             SELECT * FROM t16 AS _ WHERE "f0" IS NOT NULL)
            AS _)
           AS _
           UNION
           SELECT *
           FROM
           (SELECT
            NULL::integer AS f0, NULL::integer AS f1, f1 AS f2, f2 AS f3
            FROM
            (-- dist2
             SELECT * FROM t16 AS _ WHERE "f1" IS NOT NULL)
            AS _)
           AS _)
          AS _)
         AS _)
        AS _)
       AS _
       WHERE
       ("f2" IS NOT NULL) AND ("f3" IS NOT NULL))
      AS _)
     SELECT * FROM recursion ORDER BY step DESC LIMIT 1)
    AS _)
   SELECT *
   FROM
   (WITH t26 AS
    (SELECT *
     FROM
     (-- undist
      SELECT *
      FROM
      (SELECT
       f0 AS f0, NULL::integer AS f1, f1 AS f2
       FROM
       (-- undist1
        SELECT * FROM t0 AS _ WHERE "f0" IS NOT NULL)
       AS _)
      AS _
      UNION
      SELECT *
      FROM
      (SELECT
       NULL::integer AS f0, f2 AS f1, f3 AS f2
       FROM
       (-- dist2
        SELECT * FROM t0 AS _ WHERE "f2" IS NOT NULL)
       AS _)
      AS _)
     AS _)
    SELECT *
    FROM
    (WITH t27 AS
     (SELECT *
      FROM
      (SELECT *
       FROM
       (SELECT
        f0 AS f0, f1 AS f1
        FROM
        (WITH t28 AS
         (SELECT * FROM t26 AS _)
         SELECT *
         FROM
         (WITH t29 AS
          (SELECT *
           FROM
           (SELECT *
            FROM
            (SELECT
             f0 AS f0
             FROM
             (WITH t30 AS
              (SELECT * FROM (SELECT f0 AS f0, f1 AS f1 FROM t28 AS _) AS _)
              SELECT *
              FROM
              (SELECT *
               FROM
               (SELECT
                f0 AS f0
                FROM
                (-- join1
                 SELECT * FROM t30 AS _ WHERE "f0" IS NOT NULL)
                AS _)
               AS _
               UNION
               SELECT *
               FROM
               (SELECT
                f1 AS f0
                FROM
                (-- join2
                 SELECT * FROM t30 AS _ WHERE "f1" IS NOT NULL)
                AS _)
               AS _)
              AS _)
             AS _)
            AS _
            CROSS JOIN
            (SELECT f0 AS f1, f1 AS f2, f2 AS f3 FROM t28 AS _))
           AS _)
          SELECT *
          FROM
          (WITH t31 AS
           (SELECT *
            FROM
            (SELECT *
             FROM
             (SELECT
              f0 AS f0, f1 AS f1
              FROM
              (WITH t32 AS
               (SELECT *
                FROM
                (SELECT
                 f0 - f1 AS f0
                 FROM
                 (WITH t33 AS
                  (SELECT * FROM t29 AS _)
                  SELECT *
                  FROM
                  (SELECT *
                   FROM
                   (SELECT f0 AS f0 FROM (SELECT f0 AS f0 FROM t33 AS _) AS _)
                   AS _
                   CROSS JOIN
                   (SELECT f0 AS f1 FROM (SELECT 100 as f0 FROM t33 AS _) AS _))
                  AS _)
                 AS _)
                AS _)
               SELECT *
               FROM
               (SELECT *
                FROM
                (SELECT
                 abs(f0) as f0, NULL::integer as f1
                 FROM
                 t32
                 AS _
                 WHERE
                 f0 < 0)
                AS _
                UNION
                SELECT *
                FROM
                (SELECT NULL::integer as f0, f0 as f1 FROM t32 AS _ WHERE f0 >= 0)
                AS _)
               AS _)
              AS _)
             AS _
             CROSS JOIN
             (SELECT f0 AS f2, f1 AS f3, f2 AS f4, f3 AS f5 FROM t29 AS _))
            AS _)
           SELECT *
           FROM
           (WITH t34 AS
            (SELECT *
             FROM
             (SELECT *
              FROM
              (SELECT
               f0 AS f0, f1 AS f1
               FROM
               (SELECT f0 AS f0, f1 AS f1 FROM t31 AS _)
               AS _)
              AS _
              CROSS JOIN
              (SELECT
               f0 AS f2, f1 AS f3, f2 AS f4, f3 AS f5, f4 AS f6, f5 AS f7
               FROM
               t31
               AS _))
             AS _)
            SELECT *
            FROM
            (WITH t35 AS
             (SELECT *
              FROM
              (-- dist
               SELECT *
               FROM
               (SELECT
                f0 AS f0, f2 AS f1, NULL::integer AS f10, NULL::integer AS f11, NULL::integer AS f12, NULL::integer AS f13, f3 AS f2, f4 AS f3, f5 AS f4, f6 AS f5, f7 AS f6, NULL::integer AS f7, NULL::integer AS f8, NULL::integer AS f9
                FROM
                (-- dist1
                 SELECT * FROM t34 AS _ WHERE "f0" IS NOT NULL)
                AS _)
               AS _
               UNION
               SELECT *
               FROM
               (SELECT
                NULL::integer AS f0, NULL::integer AS f1, f4 AS f10, f5 AS f11, f6 AS f12, f7 AS f13, NULL::integer AS f2, NULL::integer AS f3, NULL::integer AS f4, NULL::integer AS f5, NULL::integer AS f6, f1 AS f7, f2 AS f8, f3 AS f9
                FROM
                (-- dist2
                 SELECT * FROM t34 AS _ WHERE "f1" IS NOT NULL)
                AS _)
               AS _)
              AS _)
             SELECT *
             FROM
             (SELECT *
              FROM
              (SELECT
               NULL::integer AS f0, f0 AS f1
               FROM
               (SELECT
                f0 + f1 AS f0
                FROM
                (WITH t36 AS
                 (SELECT *
                  FROM
                  (SELECT
                   f0 AS f0, f1 AS f1, f2 AS f2, f3 AS f3, f4 AS f4, f5 AS f5, f6 AS f6
                   FROM
                   (-- join1
                    SELECT * FROM t35 AS _
                    WHERE
                    ("f0" IS NOT NULL) AND ((("f1" IS NOT NULL) OR ("f2" IS NOT NULL)) AND (("f3" IS NOT NULL) AND ((("f4" IS NOT NULL) OR ("f5" IS NOT NULL)) AND ("f6" IS NOT NULL)))))
                   AS _)
                  AS _)
                 SELECT *
                 FROM
                 (SELECT *
                  FROM
                  (SELECT
                   f0 AS f0
                   FROM
                   (SELECT
                    f0 AS f0
                    FROM
                    (SELECT
                     f2 AS f0, f3 AS f1, f4 AS f2, f5 AS f3
                     FROM
                     (SELECT
                      f1 AS f0, f2 AS f1, f3 AS f2, f4 AS f3, f5 AS f4, f6 AS f5
                      FROM
                      t36
                      AS _)
                     AS _)
                    AS _)
                   AS _)
                  AS _
                  CROSS JOIN
                  (SELECT f0 AS f1 FROM (SELECT 1 as f0 FROM t36 AS _) AS _))
                 AS _)
                AS _)
               AS _)
              AS _
              UNION
              SELECT *
              FROM
              (SELECT
               f0 AS f0, NULL::integer AS f1
               FROM
               (SELECT
                f0 AS f0
                FROM
                (SELECT
                 f2 AS f0, f3 AS f1, f4 AS f2, f5 AS f3
                 FROM
                 (SELECT
                  f1 AS f0, f2 AS f1, f3 AS f2, f4 AS f3, f5 AS f4, f6 AS f5
                  FROM
                  (SELECT
                   f7 AS f0, f8 AS f1, f9 AS f2, f10 AS f3, f11 AS f4, f12 AS f5, f13 AS f6
                   FROM
                   (-- join2
                    SELECT * FROM t35 AS _
                    WHERE
                    ("f7" IS NOT NULL) AND ((("f8" IS NOT NULL) OR ("f9" IS NOT NULL)) AND (("f10" IS NOT NULL) AND ((("f11" IS NOT NULL) OR ("f12" IS NOT NULL)) AND ("f13" IS NOT NULL)))))
                   AS _)
                  AS _)
                 AS _)
                AS _)
               AS _)
              AS _)
             AS _)
            AS _)
           AS _)
          AS _)
         AS _)
        AS _)
       AS _
       CROSS JOIN
       (SELECT f0 AS f2 FROM (SELECT f2 AS f0 FROM t26 AS _) AS _))
      AS _)
     SELECT *
     FROM
     (-- dist
      SELECT *
      FROM
      (SELECT
       f0 AS f0, f2 AS f1, NULL::integer AS f2, NULL::integer AS f3
       FROM
       (-- dist1
        SELECT * FROM t27 AS _ WHERE "f0" IS NOT NULL)
       AS _)
      AS _
      UNION
      SELECT *
      FROM
      (SELECT
       NULL::integer AS f0, NULL::integer AS f1, f1 AS f2, f2 AS f3
       FROM
       (-- dist2
        SELECT * FROM t27 AS _ WHERE "f1" IS NOT NULL)
       AS _)
      AS _)
     AS _)
    AS _)
   AS _)
  AS _
  WHERE
  ("f0" IS NOT NULL) AND ("f1" IS NOT NULL))
 AS _)
AS _;
```

</details>

It's not pretty, rather amazingly, running the above query in postgres 17 will
in fact return a single row with a single column whose value is 100. And you'd
better believe it does it by *actually looping its way up to 100.* If you don't
believe me, make the following change:

```diff
-     SELECT * FROM recursion ORDER BY step DESC LIMIT 1)
+     SELECT * FROM recursion ORDER BY step DESC)
```

which will instead return a row for each step of the iteration.

There are some obvious optimizations I could make to the generated SQL, but it
didn't seem worth my time, since that's not the interesting part of the project.


## What the Hell Is Going On?

Let's take some time to discuss the underlying category theory here. I am by no
means an expert, but what I have learned after a decade of bashing my head
against this stuff is that a little goes a long way.

For our intents and purposes, we have types, and arrows (functions) between
types. We always have the identity "do nothing arrow" `id`:

```haskell
id  :: a ~> a
```

and we can compose arrows by lining up one end to another:[^metatheory]

[^metatheory]: When looking at the types of arrows in this essay, we make the
distinction that `~>` are arrows that we can write in catlang, while `->` exist
in the metatheory.

```haskell
(⨟) :: (a ~> b) -> (b ~> c) -> (a ~> c)
```

Unlike Haskell (or really any programming language, for that matter), we DO NOT
have the notion of function application. That is, there is no arrow:

```haskell
-- doesn't exist!
($) :: (a ~> b) -> a -> b
```

You can only compose arrows, you can't apply them. That's why we call these
things "arrows" rather than "functions."

There are a bundle of arrows for working with product types. The two projection
functions correspond to `fst` and `snd`, taking individual components out of
pairs:

```haskell
prj₁ :: (a, b) ~> a
prj₂ :: (a, b) ~> b
```

How do we get things into pairs in the first place? We can use the "fork"
operation, which takes two arrows computing `b` and `c`, and generates a new
arrow which generates a pair of `(b, c)`:

```haskell
(△)  :: (a ~> b) -> (a ~> c) -> (a ~> (b, c))
```

If you're coming from a Haskell background, it's tempting to think of this
operation *merely* as the `(,)` pair constructor. But you'll notice from the
type of the computation that there can be no data dependency between `b` and
`c`, thus we are free to parallelize each side of the pair.

In category theory, the distinction between left and right sides of an arrow is
rather arbitrary. This gives rise to a notion called *duality* where we can flip
the arrows around, and get cool new behavior. If we dualize all of our product
machinery, we get the *coproduct* machinery, where a coproduct of `a` and  `b`
is "either `a` or `b`, but definitely not both nor neither."

Swapping the arrow direction of `prj₁` and `prj₂`, and replacing `(,)` with
`Either` gives us the following injections:

```haskell
inl :: a ~> Either a b
inr :: b ~> Either a b
```

and the following "join" operation for eliminating coproducts:

```haskell
(▽) :: (a ~> c) -> (b ~> c) -> (Either a b ~> c)
```

Again, coming from Haskell this is just the standard `either` function. It
corresponds to a branch between one of two cases.

As you can see, with just these eight operations, we already have a tremendous
amount of expressivity. We can express data dependencies via `⨟` and branching
via `▽`. With `△` we automatically encode opportunities for parallelism, and
gain the ability to build complicated data structures, with `prj₁` and `prj₂`
allowing us to get the information *back out* of the data structures.

You'll notice in the IL that there are no variable names anywhere to be found.
The desugaring of the source language builds a stack (via the `something to
allocate △ id` pattern), and replaces subsequent variable lookups with a series
of projections on the stack to find the value again. On one hand, this makes the
categorical IL rather hard to read, but it makes it very easy to re-target! Many
domains do have a notion of grouping, but don't have a native notion of naming.

For example, in an electronic circuit, I can have a ribbon of 32 wires which
represents an `Int32`. If I have another ribbon of 32 wires, I can trivially
route both wires into a 64-wire ribbon corresponding to a pair of `(Int32,
Int32)`.

By eliminating names before we get to the IL, it means no compiler backend ever
needs to deal with names. They can just work on a stack representation, and are
free to special-case optimize series of projections if they are able to.

Of particular interest to this discussion is how we desugar loops in catlang.
The underlying primitive is `cochoice`:

```haskell
cochoice :: (Either a c ~> Either b c) -> (a ~> b)
```

which magically turns an arrow on `Either`s into an arrow without the eithers.
We obviously must *run* that arrow on eithers. If that function returns `inl`,
then we're happy and we can just output that. But if the function returns `inr`,
we have no choice but to pass it back in to the eithered arrow. In Haskell,
cochoice is implemented as:

```haskell
cochoiceHask :: (Either a c -> Either b c) -> a -> c
cochoiceHask f = go . Left
  where
    go :: Either a c -> b
    go eac =
      case f eac of
        Left b -> b
        Right c -> go (Right c)
```

which as you can see, will loop until `f` finally returns a `Left`. What's neat
about this formulation of a loop is that we can statically differentiate between
our first and subsequent passes through the loop body. The first time through
`eac` is `Left`, while for all other times it is `Right`. We don't take
advantage of it in the original `count` program, but how many times have you
written loop code that needs to initialize something its first time through?


## Compiling to SQL

So that's the underlying theory behind the IL. How can we compile this to SQL
now?

As alluded to before, we simply need to give SQL implementations for each of the
operations in the intermediary language. As a simple example, `id` compiles to
`SELECT * FROM {}`, where `{}` is the input of the arrow.

The hardest part here was working out a data representation. It seems obvious to
encode each element of a product as a new column, but what do we do about
coproducts? After much work thought, I decided to flatten out the coproducts.
So, for example, the type:

```haskell
(Int, Either Int Int)
```

would be represented as three columns:

```sql
( f1 INT NOT NULL
, f2 INT
, f3 INT
)
```

with the constraint that exactly one of `f2` or `f3` would be `IS NOT NULL` at
any given point in time.

With this hammered out, almost everything else is pretty trivial. Composition
corresponds to a nested query. Forks are `CROSS JOIN`s which concatenate the
columns of each sub-query. Joins are `UNION`s, where we add a `WHERE field IS
NOT NULL` clause to enforce we're looking at the correct coproduct constructor.

Cochoice is the only really tricky thing, but it corresponds to a [recursive
CTE](https://www.postgresql.org/docs/current/queries-with.html#QUERIES-WITH-RECURSIVE).
Generating a recursive CTE table for the computation isn't too hard, but getting
the final value out of it was surprisingly tricky. The semantics of SQL tables
is that they are multisets and come with an arbitrary greatest element. Which is
to say, you need an column structured in a relevant way in order to query the
final result. Due to some quirks in what postgres accepts, and in how I
structured my queries, it was prohibitively hard to insert a "how many times
have I looped" column and order by that. So instead I cheated and added a
`clock_timestamp() as step` column which looks at the processor clock and
ordered by that.

This is clearly a hack, and presumably will cause problems if I ever add some
primitives which generate more than one row, but again, this is just for fun and
who cares. Send me a [pull request](https://github.com/isovector/catlang) if
you're offended by my chicanery!


## Stupid Directions To Go In the Future

I've run out of vacation time to work on this project, so I'm probably not going
to get around to the meta-circular stupidity I was planning.

The compiler still needs a few string-crunching primitives (which are easy to
add), but then it would be simple to write a little
[brainfuck](https://en.wikipedia.org/wiki/Brainfuck) interpreter in catlang.
Which I could then compile to SQL. Now we've got a brainfuck interpreter running
in postgres. Of course, this has been done by hand before, but to my knowledge,
never via compilation.

There exist C to brainfuck compilers. And postgres is written in C. So in a move
that would make Xzibit proud, we could run postgres in postgres. And of course,
it would be fun to run brainfuck in brainfuck. That'd be a cool catlang backend
if someone wanted to contribute such a thing.


## Notes and Due Diligence and What Have You

I am not the first person to do anything like this. The source language of
catlang is heavily inspired by [Haskell's arrow
syntax](https://www.staff.city.ac.uk/~ross/papers/notation.pdf), which in turn
is essentially a desugaring algorithm for
[Arrows](https://www.cse.chalmers.se/~rjmh/afp-arrows.pdf). Arrows are slightly
the wrong abstraction because they require an operation `arr :: (a -> b) -> (a
~> b)`---which requires you to be able to embed Haskell functions in your
category, something which is *almost never possible.*

Unfortunately, arrow syntax in Haskell desugars down to `arr` for almost
everything it does, which in turn makes arrow notation effectively useless. In
an ideal world, everything I described in this blog post would be a tiny little
Haskell library, with arrow notation doing the heavy lifting. But that is just
not the world we live in.

Nor am I the first person to notice that there are categorical semantics behind
programming languages. I don't actually know whom to cite on this one, but it is
well-established folklore that the lambda calculus corresponds to
[cartesian-closed
categories](https://en.wikipedia.org/wiki/Cartesian_closed_category). The
"closed" part of "cartesian-closed" means we have an operation `eval :: (a ~> b,
a) ~> b`, but everyone and their dog has implemented the lambda calculus, so I
thought it would be fun to see how far we can get without it. This is not a
limitation on catlang's turing completeness (since `cochoice` gives us
everything we need.)

I've been thinking about writing a *category-first* programming language for the
better part of a decade, ever since I read [Compiling to
Categories](http://conal.net/papers/compiling-to-categories/compiling-to-categories.pdf).
That paper takes Haskell and desugars it back down to categories. I stole many
of the tricks here from that paper.

Anyway. All of the code is available on
[github](https://github.com/isovector/catlang) if you're interested in taking a
look. The repo isn't up to my usual coding standards, for which you have my
apologies. Of note is the template-haskell backend which can spit out Haskell
code; meaning it wouldn't be very hard to make a quasiquoter to compile catlang
into what Haskell's arrow desugaring *ought to be.* If there's enough clamor for
such a thing, I'll see about turning this part into a library.

