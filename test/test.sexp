(module
    ()
    (def test ()
        (let val
            (inst (test test ret4))
            (ap (lambda (x) (local x)) val)
        )
    )
    (def ret4 ()
        (iu64 3)
    )

    (def make_pair ()
        (iprod (fst (iunit)) (snd (inst (test test ret4))))
    )
    (def fst ()
        (expr
            (lambda (x)
                (mprod (fst snd) (fst snd) (local x) (local fst))
            )
            (ty (ffunc pair
                (fprod (fst (funit)) (snd (fu64)))
                (var 0)
            ))
        )
    )
    (def use_fst ()
        (let pair
            (inst (test test make_pair))
            (ap (inst (test test fst)) pair)
        )
    )

    (def MyPair ()
        (fprod (fst (funit)) (snd (fu64)))
    )
    (def make_my_pair ()
        (expandty
            (inst (test test make_pair))
            (inst (test test MyPair))
        )
    )
    (def use_my_pair ()
        (reducety
            (inst (test test make_my_pair))
            (fprod (fst (funit)) (snd (fu64)))
        )
    )
    (def id_MyPair ()
        (expr
            (lambda (x) (local x))
            (ty (ffunc pair (inst (test test MyPair)) (var 1)))
        )
    )

    (def OptionInt ()
        (fcoprod (Some (fu64)) (None (funit)))
    )
    (def some_int ()
        (lambda (i)
            (expandty
                (icoprod (Some (local i)))
                (inst (test test OptionInt))
            )
        )
    )

    (def unwrap_or_zero ()
        (expr
            (lambda (pair)
                (mcoprod
                    (val none)
                    (reducety
                        (local pair)
                        (fcoprod (Some (fu64)) (None (funit)))
                    )
                    (
                        (Some (local val))
                        (None (iu64 0))
                    )
                )
            )
            (ty
                (ffunc pair
                    (inst (test test OptionInt))
                    (var 2)
                )
            )
        )
    )

    (def Option ()
        (lambda (T)
            (fcoprod (Some (local T)) (None (funit)))
        )
    )
    (def some ()
        (lambda (T)
            (lambda (x)
                (expr
                    (icoprod (Some (local x)))
                    (ty (fcoprod (Some (local T)) (None (funit))))
                )
            )
        )
    )
)
