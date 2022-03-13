(module
    ()
    (def "test" ()
        (let
            (inst ("test" "test" "ret4"))
            (ap (lambda 1 (local 0)) 0)
        )
    )
    (def "ret4" ()
        (iu64 3)
    )
)
