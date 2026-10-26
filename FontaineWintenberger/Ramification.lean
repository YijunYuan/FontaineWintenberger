/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Different.Hilbert
public import FontaineWintenberger.Ramification.Different.Monogenic
public import FontaineWintenberger.Ramification.Different.Subextension
public import FontaineWintenberger.Ramification.Different.TraceIdeal
public import FontaineWintenberger.Ramification.Embedding.Basic
public import FontaineWintenberger.Ramification.Embedding.Valued
public import FontaineWintenberger.Ramification.Fields.Inertia
public import FontaineWintenberger.Ramification.Fields.Nonnormal
public import FontaineWintenberger.Ramification.Fields.PrimeTower
public import FontaineWintenberger.Ramification.Fields.Tame
public import FontaineWintenberger.Ramification.Fields.Wild
public import FontaineWintenberger.Ramification.Herbrand.Affine
public import FontaineWintenberger.Ramification.Herbrand.Basic
public import FontaineWintenberger.Ramification.Herbrand.Interval
public import FontaineWintenberger.Ramification.Herbrand.Inverse
public import FontaineWintenberger.Ramification.Herbrand.Subgroup
public import FontaineWintenberger.Ramification.Infinite.Basic
public import FontaineWintenberger.Ramification.Infinite.Limit
public import FontaineWintenberger.Ramification.Infinite.Restriction
public import FontaineWintenberger.Ramification.Infinite.SplittingField
public import FontaineWintenberger.Ramification.Lower.BaseChange
public import FontaineWintenberger.Ramification.Lower.Basic
public import FontaineWintenberger.Ramification.Lower.Degree
public import FontaineWintenberger.Ramification.Lower.FiniteResidue
public import FontaineWintenberger.Ramification.Lower.FixedField
public import FontaineWintenberger.Ramification.Lower.GaloisGroup
public import FontaineWintenberger.Ramification.Lower.Generator
public import FontaineWintenberger.Ramification.Lower.Index
public import FontaineWintenberger.Ramification.Lower.Inertia
public import FontaineWintenberger.Ramification.Lower.ResidueDigits
public import FontaineWintenberger.Ramification.Lower.SpectralMaps
public import FontaineWintenberger.Ramification.Lower.Tame
public import FontaineWintenberger.Ramification.Lower.Teichmuller
public import FontaineWintenberger.Ramification.Lower.TotalRamification
public import FontaineWintenberger.Ramification.Lower.Tower
public import FontaineWintenberger.Ramification.Lower.TruncatedCoefficients
public import FontaineWintenberger.Ramification.Lower.Uniformizer
public import FontaineWintenberger.Ramification.Lower.Wild
public import FontaineWintenberger.Ramification.Norm.Approximation
public import FontaineWintenberger.Ramification.Norm.Congruence
public import FontaineWintenberger.Ramification.Norm.Tower
public import FontaineWintenberger.Ramification.Norm.Valuation
public import FontaineWintenberger.Ramification.Upper.BaseChange
public import FontaineWintenberger.Ramification.Upper.Basic
public import FontaineWintenberger.Ramification.Upper.CosetMax
public import FontaineWintenberger.Ramification.Upper.FixedField
public import FontaineWintenberger.Ramification.Upper.PrimeOrder
public import FontaineWintenberger.Ramification.Upper.Quotient
public import FontaineWintenberger.Ramification.Upper.ResidueEquiv
public import FontaineWintenberger.Ramification.Upper.Tate
public import FontaineWintenberger.Ramification.Upper.Transport

/-!
# Ramification of local-field extensions

This module collects lower and upper ramification groups, Herbrand functions, the different,
and norm estimates for finite and infinite extensions, following Serre's *Local Fields*.
-/
