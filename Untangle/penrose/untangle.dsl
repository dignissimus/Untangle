type FunctorLike
type NaturalTransformationLike

predicate Apply(FunctorLike left, FunctorLike right)
predicate Transform(FunctorLike F, NaturalTransformationLike alpha)
predicate WouldTransform(FunctorLike F, NaturalTransformationLike alpha)
predicate Next(FunctorLike F, FunctorLike G)
predicate Out(NaturalTransformationLike alpha, FunctorLike F)
predicate Connect(FunctorLike F, FunctorLike G)
predicate Braid(NaturalTransformationLike alpha)