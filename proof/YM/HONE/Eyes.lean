import YM.HONE.Bird
import YM.HONE.Pulse
import YM.HONE.Pulse
import YM.HONE.Stand
import YM.Lyre.Ascent
import YM.Lyre.Pillar
import YM.Lyre.Bloom
set_option autoImplicit false
noncomputable section
namespace YM.Intag.CardsT
open Function Filter Finset MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Lat QCD.Tide Push.GridApprox
open QCD.Grass QCD.Plum
open MassiveQCD MassiveQCD.Cupola MassiveQCD.Sample Sample.LoomT Sample.Quills
open QCD.Acre.Stratum.MarchQ.Suburb.Melt.Lobby
open scoped BigOperators Classical
variable {S:Scheme}{R:Side}{ℓ i k n:ℕ}{I:Type} [Fintype I] (A:Massive.Run S n R 6)
variable (X:I→ Cover) (U:I→ Averaging)(q:I→Bool)
local notation "H" k:arg=> Hole I S ℓ k
local notation "p" k:arg=> showX S ℓ k X
local notation "L" k:arg=> CardsT.link S ℓ k X
variable (w:∀ k:ℕ,Hole I S ℓ (k+1)→Hole I S ℓ k→ℝ)
variable (hw: ∀ k,ℓ ≤ k → SignedWeights S ℓ k X U (w k))
local notation "Sn"=> S.side R
set_option quotPrecheck false
variable (F:I → Cover → Insertion (S.side R n) 6) -- true ordered list tests
-- stage sensor.L.V ephemeral transport. choose left mass-density placement convention.

local notation "Pr"=>A.regulator.density
variable (Ψ:I → Cover → Insertion (S.side R k) 6)
variable (hA:A.Actual)(h:k≤n)
local notation "YC"=> fruitT A X U q w F Ψ
local notation "Qr" j:arg=> CardsT.stencil (I:=I) S ℓ j
local notation "VQ" jx:arg=> doubleT A X U F Ψ (i:=jx)
variable (hs:ℓ ≤ i)(hi:i≤ k)
open Massive.Patria.Rolls QCD.Tide Massive.Patria
local notation "κ"=> Tally
local notation "g"=> Pr
-- genuine matching transform any Primary.Budget Beacons in reality. Wants neither Fake startup.
variable (a:Axis)(Jv:Massive.Averaging)(X Y:Cover→ Insertion (S.side R k) 6)
open QCD.Revolve Poised Canvas Exposure Cylinder
local notation "T"=> tentT A Jv
variable (hX:∀ b:Cover,  Massive.Cylinder.Action.adj a ⇑(X b)= Y ((Signed.mirror a).act b))(Mv:ℕ)
variable {d:ℕ}(μ:UV.Label d)(W:SourceRead.TaperHol)(B:Bore d)(P:UV.RawSym)(hf:Rubric P B)
local notation "Φ"=>Signed.mirror a
include hA h hi hX
set_option maxHeartbeats 580000 in
lemma nourish : Action.adj a ((T X) i 0)=(T Y) i 0:=by
    let B₀:= densityW A k; let f1(b:Cover):= X b*B₀; let f2(b:Cover):=Y b*B₀; let Z1:=visitor S k i Jv 0 f1; let Z2:=visitor S k i Jv 0 f2
    let Sv:=S.side R k; have hx: ∀ b:Cover,Action.adj a (f1 b)= f2 ((Φ).act b):=by
         intro b; let F:= tilt (eyeP Sv a); have hy:Action.adj a B₀=B₀:= (arrives A k h).2.1 _; have h0(U): Plus (B₀ U):=by have he:(A.density k)= B₀:= pier A hA h; rw[show B₀ U=A.density k U from (congr_fun he U).symm]; exact hA.even h U
         funext U; rw[eye_value]; let U':=pull (K:=su.El) (Φ) 0 U; change F ((X b U')*(B₀ U'))= Y _ _* _; rw[show F ((X b U')*(B₀ U'))= F (B₀ U')*F (X b U') from tilt_mul .., show F (B₀ U')=B₀ U from (eye_value ..).symm.trans (congr_fun hy U), show F (X b U')= _ from (show F (X b U')=Y ((Φ).act b) U from (eye_value ..).symm.trans (congr_fun (hX b) U))]; exact ((h0 U).central _).symm.eq
    have ht: Action.adj a Z1 = Z2:=by
         funext U; unfold Z1 Z2 visitor; rw [smul_zero]; let V:=pull (K:=su.El) Φ 0 U
         let Qb:= ((realTilt (c:=Sv) (eyeP Sv a)).comp (ContinuousMap.evalCLM ℝ V)).toLinearMap; have hy(x:Cover): Qb (f1 x)= f2 ((Φ).act x) U :=(eye_value (f1 x) a U).symm.trans (congr_fun (hx x) U)
         rw[eye_value]; have h:=permeate Jv Φ Qb f1 f2 U hy (odd_to (S:=S) hi); rw [permit_mirror] at h; exact h
    change Action.adj a (relay A i Z1)=relay A i Z2
    clear_value Z1 Z2
    induction hi using Nat.decreasingInduction with
    | self=> unfold relay; rw [S.entrance]; exact ht
    | of_succ i h ih => rw [stepped A Z1 h,stepped A Z2 h]; unfold Run.block; rw [step_brute,step_brute]; rw[eye_shift _ _ _ (S.admissible i) _ _ (ContinuousMap.continuous _),ih] -- signature
-- period. Beacon living at i via W.Material pinned read.
include hf
lemma resolveY (Q:Market S R d)(hW:Wager A W B Q i) (he: Tally W 0 μ (A.density i) ((T X) i 0)) : Tally W 0 (P.adj d a μ) (A.density i) ((T Y) i 0):=by
      have ht:= pier A hA hW.siteM
      rw [← nourish A hA h hi a Jv X Y hX]; have hv:= arrives A i hW.siteM; exact Canvas.flux W _ a hW.living _ (fun x:UV.Label d=>⇑(B (S.side R i) 0 x)) he hW.reading (by rw[ht]; exact hv.2.1 a) (by rw[ht]; exact hv.2.2.2.2) (by have hh:=hf.eye (S.side R i) μ 0 a; rw [Signed.act_zero] at hh; exact hh)
end YM.Intag.CardsT
#print axioms YM.Intag.CardsT.resolveY
