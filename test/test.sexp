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

    (def pair_unit_int ()
        (fprod (comp fst (funit)) (comp snd (fu64)))
    )
    (def make_pair ()
        (iprod (fst (iunit)) (snd (iu64 10)))
    )
)
