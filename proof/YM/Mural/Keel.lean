import YM.Mural.Knur
import YM.Massive.PCAC.Mixed
/-! # Actual field data carriers. No invariant on opaque Rank needed: source always one open mass-color. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG
open Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine NormedSpace
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open MassiveQCD MassiveQCD.Apron.Grove Plette Lat
open PaletteT Ribbon
variable {c f:Side}{j k N:ℕ}
open QCD.Mural MassiveQCD.Stitch MassiveQCD.Apron.Grove.PrintR Plate Cupola Twist Kites Creek Cove
/- A Frame standing in one layer of course.$R.O$ at arb level. Contains actual unweighted radial.K weights handled by scalar `w` to carry.Ph.Coherence Census -/
structure DeckV (c:Side) (N:ℕ) where
   I : Type
   E: Grid c→ EvenA c N
   K: Patron.Rail c N I
   O:BudgetPoint
namespace DeckV
noncomputable def density (D:DeckV c N) (X:Grid c):= (exp (D.E X)*heartK D.K D.O.threshold X).val
noncomputable def emblem (D:DeckV c N) {I E:Type} (Z:PrintR c N Rank I E)(i:Option Rank)(s:Finset (Spine Unit))(U:Grid c): Fields c N:= pluck (Keys c N) s (relativeE N (Z.regE i) (Z.regK i) D.K D.E D.O.threshold U)
end DeckV
variable {I E:Type}(Z:PrintR c N Rank I E)(D:DeckV c N)
local notation "dr"=> D.density
local notation "E!"=> D.emblem Z
local notation "Kx"=> Keys c N
local notation "R"=> Ribbon.Spine Unit
variable {t a b v b' v' w η x:ℝ}
variable (W:Unit→Site c) (S:Support c)(Q:Lat.Frame c→Delta Rank)(hP:Z.Fides W S D.O Q)(hp:∀ U,Summable (fun j=>‖D.K.warp j U‖)) (h:Z.Levy D.O t a b v w η x)
include hP hp h
lemma tiltP (ht:1≤t)(ha:1 ≤ a)(hv:0≤v)(hb:0 ≤ b)(hy:1 ≤η)(U:Grid c)(i:Option Rank): E! i ∅ U=dr U:= by
    have hm i:=billP Z U D.O a t b v w η x h ha hy ht hb hv i -- wrong order b d p v h check
    let K:=trestle Z (fun _=>0) (fun _=>0) 0
    have hx:K.Levy D.O t a b v 0 η 0:=by
         have hU := esteem Z (fun _=>0) (fun _=>0) 0 _ b 0 v a η w x t h (fun i j k=> by simp) η (zero_le_one.trans hy) le_rfl b v le_rfl le_rfl
         simpa using hU
    have Hx i:=billP K U D.O a t b v 0 η 0 hx ha hy ht hb hv i
    exact primus Z (fun _=>0) (fun _=>0) 0 U D.O S W Q D.K D.E (hp U) hP (fun i=>(hm i).1) (fun i=>(hm i).2) (fun i=>(Hx i).1) (fun i=>(Hx i).2) i
omit hP hp h
lemma grant_high (hp: Z.Levy D.O t a b v w η x) (hb:w ≤ b')(hv:x ≤ v') : Z.Levy D.O t a b v b' η v':=by
    refine ⟨fun i=>?_ ,fun i=>?_⟩; · obtain ⟨g,hg,hG⟩:=hp.budget i; exact ⟨g,hg,fun i=>Push.AbsoluteSums.budget_loosen (hG i) hb⟩
    obtain ⟨g,hg,hG⟩:=(hp.fare i).price; exact ⟨g,hg,fun i=>Push.AbsoluteSums.budget_loosen (hG i) hv⟩
open Massive Massive.PCAC
-- Step spin projection via fields.Birth/continuation.
variable (D':DeckV f N)(L: YM.Next.Free.Flight j k) (d:f.val=c.val*L.L.val)(K:KernelChoices)(r β:ℝ) (hk:L.patch.Branches K su)
local notation "S'"=> (L.visit K d)
local notation "WE"=> DeckV.emblem
variable (X:PrintR f N Rank I E)
variable {Ic Ec:Type}(P: PrintR c N Rank Ic Ec)(C:ℂ)(Φ:Option Rank→Grid f→ Grid c→ℂ)
open QCD.Jets
structure Strike : Prop where
   roll: ∀ i V s, Kites.engine r Kx ((S').push β (fun U=> Kit.sheath 1 (ater L d U) (WE D' X i s U)+ if s=sD then Φ i U V • Kit.sheath 1 (ater L d U) (WE D' X i ∅ U) else 0) V)= C • WE D P i s V
local notation "Φy"=> Transfer.blockMap L K d β r hk
variable {α₀:ℂ}
local notation "y"=> D'.density
variable (Y: Insertion f N)(Y':Insertion c N)(ht:Y'= (Transfer.blockMap L K d β r hk) Y)
include hk
lemma extendT {U:Grid c}(X:Insertion f N) (vX:Grid f→ Fields c N) (he:∀ V:Grid f,Kit.sheath 1 (ater L d V) (X V)= vX V) : Φy X U= engine r Kx ((S').push β vX U):= by
     change Massive.rescale r _=_; have hx:soften L d ⇑X=vX:=funext he; change Massive.rescale r ((S').push β (soften L d ⇑X) _)= _; rw [hx]; rfl -- typo
include ht
variable (hK:∀ U,Y U= α₀ • D'.density U)(hw:Strike D D' L d K r β X P C Φ)
include hw hK
-- base settlement
lemma plainLoad (i:Option Rank) (hx:∀ U:Grid f,D'.emblem X i ∅ U=D'.density U)(he:∀ U:Grid c,D.emblem P i ∅ U=D.density U) :∀ U:Grid c,Y' U=(α₀*C) • D.density U:=by
    intro U
    let g:=D'.density
    let Wz(V:Grid f):= Kit.sheath 1 (ater L d V) (WE D' X i ∅ V)
    have hp := hw.roll i U ∅; simp_rw [if_neg (show (∅:Finset R)≠sD from fun h=> (show sD.Nonempty from ⟨(((),false),0),mem_univ _⟩).ne_empty h.symm),add_zero] at hp -- invalid
    have h(Z): Wz Z= Kit.sheath 1 (ater L d Z) (g Z):=by unfold Wz; rw [hx]
    let Ry(U:Grid f):= α₀ • Wz U; rw [ht,extendT _ _ _ _ _ hk _ Ry]
    · have hm: engine r Kx ((S').push β Ry U)= α₀ • engine r Kx ((S').push β Wz U):=by
            unfold StepData.push; unfold Ry; simp_rw [smul_comm _ α₀]; rw [integral_smul,map_smul]
      rw [hm]; rw [he] at hp; -- clean term purchase x+ zero
      rw [mul_smul]; exact congr_arg _ hp
    intro v; rw [hK, ← hx]; exact congr_fun (Transfer.soften_smul L d (fun _=>WE D' X i ∅ v) α₀) v
end YM.QCD.Comet
#print axioms YM.QCD.Comet.tiltP
#print axioms YM.QCD.Comet.plainLoad
