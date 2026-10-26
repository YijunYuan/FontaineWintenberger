/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.LocalField.Hensel.NewtonLifting
public import FontaineWintenberger.LocalField.Hensel.NewtonValuation
public import FontaineWintenberger.LocalField.Hensel.RootExtraction
public import FontaineWintenberger.LocalField.Laurent.Coordinates
public import FontaineWintenberger.LocalField.Residue.Basic
public import FontaineWintenberger.LocalField.Spectral.CompatibleNorm
public import FontaineWintenberger.LocalField.Spectral.FiniteExtension
public import FontaineWintenberger.LocalField.Spectral.Henselian
public import FontaineWintenberger.LocalField.Spectral.IntegralGenerator
public import FontaineWintenberger.LocalField.Spectral.Tower
public import FontaineWintenberger.LocalField.Spectral.Transport
public import FontaineWintenberger.LocalField.Spectral.Uniqueness

/-!
# Local fields and their finite extensions

This module collects the local-field hypotheses, compatible valuations and spectral norms,
Hensel lifting, residue fields, and Laurent-series coordinates used by the field of norms.
-/
