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
        (let
            (lambda 1
                (rprod 2 (lambda 2 (local 1)) (local 0))
            )
            (let
                (inst (test test make_pair))
                (ap (local 1) 0)
            )
        )
    )
)
