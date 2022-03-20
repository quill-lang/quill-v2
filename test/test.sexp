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
                (funit)
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
)
