/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.BaseChange.Basic
public import FontaineWintenberger.APF.BaseChange.Bounds
public import FontaineWintenberger.APF.BaseChange.EmbeddingComparison
public import FontaineWintenberger.APF.BaseChange.EmbeddingFiber
public import FontaineWintenberger.APF.BaseChange.EmbeddingFiniteBase
public import FontaineWintenberger.APF.BaseChange.Strict
public import FontaineWintenberger.APF.BaseChange.UpperGroups
public import FontaineWintenberger.APF.BaseClosure
public import FontaineWintenberger.APF.Defs
public import FontaineWintenberger.APF.Elementary.FirstBreak
public import FontaineWintenberger.APF.Elementary.NormContinuity
public import FontaineWintenberger.APF.Elementary.NormPrecision
public import FontaineWintenberger.APF.Elementary.PrimeDegree
public import FontaineWintenberger.APF.Elementary.TameCompositum
public import FontaineWintenberger.APF.Finite.ConstantIndex
public import FontaineWintenberger.APF.Finite.Galois
public import FontaineWintenberger.APF.Finite.Nonnormal
public import FontaineWintenberger.APF.Finite.Slope
public import FontaineWintenberger.APF.Galois
public import FontaineWintenberger.APF.Galois.Restriction
public import FontaineWintenberger.APF.Galois.Union
public import FontaineWintenberger.APF.Herbrand
public import FontaineWintenberger.APF.Index
public import FontaineWintenberger.APF.RamificationBound
public import FontaineWintenberger.APF.Strict
public import FontaineWintenberger.APF.Subextension
public import FontaineWintenberger.APF.Tower.AlgebraicResidue
public import FontaineWintenberger.APF.Tower.PrimeValuation
public import FontaineWintenberger.APF.Tower.Residue
public import FontaineWintenberger.APF.Tower.Stages
public import FontaineWintenberger.APF.Tower.Tame
public import FontaineWintenberger.APF.Tower.TotallyRamified
public import FontaineWintenberger.APF.Tower.Wild

/-!
# Arithmetically profinite extensions

This module collects APF and strictly APF extensions, their Herbrand functions, finite base
change, and towers of elementary extensions, following §1 of Wintenberger's paper.
-/
