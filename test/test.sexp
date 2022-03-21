(module
    ()
    (def test ()
        (let
            (inst (test test ret4))
            (ap (lambda 1 (local 0)) 0)
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
            (lambda 1
                (mprod (fst snd) (local 0) (local 1))
            )
            (ty (ffunc
                (fprod (fst (funit)) (snd (fu64)))
                (var 0)
            ))
        )
    )
    (def use_fst ()
        (let
            (inst (test test make_pair))
            (ap (inst (test test fst)) 0)
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
            (lambda 1 (local 0))
            (ty (ffunc (inst (test test MyPair)) (var 1)))
        )
    )

    (def OptionInt ()
        (fcoprod (Some (fu64)) (None (funit)))
    )
    (def some ()
        (lambda 1
            (expandty
                (icoprod (Some (local 0)))
                (inst (test test OptionInt))
            )
        )
    )

    (def unwrap_or_zero ()
        (lambda 1
            (mcoprod
                (reducety
                    (expr (local 0) (ty (inst (test test OptionInt))))
                    (fcoprod (Some (fu64)) (None (funit)))
                )
                (
                    (Some (local 0))
                    (None (iu64 0))
                )
            )
        )
    )
)
