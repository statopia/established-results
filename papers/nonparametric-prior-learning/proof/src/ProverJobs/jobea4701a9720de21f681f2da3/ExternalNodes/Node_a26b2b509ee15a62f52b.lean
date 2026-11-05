import ProverJobs.jobea4701a9720de21f681f2da3.Base

-- External DAG node: ext_model_1 (AXIOM)
example : Prop := (open MeasureTheory ProbabilityTheory in (open scoped ENNReal BigOperators Topology in (∀ {H : Type*} [TopologicalSpace H] [PolishSpace H] [MeasurableSpace H] [BorelSpace H]
    (mu nu : ProbabilityMeasure H),
    ENNReal.toEReal (InformationTheory.klDiv (nu : Measure H) (mu : Measure H))
      = ⨆ (Theta : H → ℝ), ⨆ (_ : Continuous Theta),
          ⨆ (_ : Bornology.IsBounded (Set.range Theta)),
            ((↑(∫ x, Theta x ∂(nu : Measure H)) : EReal)
              - (↑(Real.log (∫ x, Real.exp (Theta x) ∂(mu : Measure H))) : EReal)))))
axiom ExternalRevision_5d5e44994e1bd0d7755f1cc92bfd67e5640cab3ee11d2f6e18ce338046e89096.citation : (open MeasureTheory ProbabilityTheory in (open scoped ENNReal BigOperators Topology in (∀ {H : Type*} [TopologicalSpace H] [PolishSpace H] [MeasurableSpace H] [BorelSpace H]
    (mu nu : ProbabilityMeasure H),
    ENNReal.toEReal (InformationTheory.klDiv (nu : Measure H) (mu : Measure H))
      = ⨆ (Theta : H → ℝ), ⨆ (_ : Continuous Theta),
          ⨆ (_ : Bornology.IsBounded (Set.range Theta)),
            ((↑(∫ x, Theta x ∂(nu : Measure H)) : EReal)
              - (↑(Real.log (∫ x, Real.exp (Theta x) ∂(mu : Measure H))) : EReal)))))
