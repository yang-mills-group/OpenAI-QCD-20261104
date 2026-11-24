import YM.Oars.Canyon
import YM.Oars.Planetaria
import YM.Oars.Plucks
import YM.Cardinal.Doss
import YM.Cardinal.Ear
/-! # Large/small address reunion for a Painted Reel, general marker set -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{m k l N:ℕ} {I J U E:Type}[Fintype I]
variable {a A C v w t t₁ t₂:ℝ}{O: BudgetPoint}
variable (N)(p:I→Site c)(q:I→Bool)(θ φ r:ℝ)
local notation "M"=> Ribbon.ample N I
variable (Y: Ruby.Hue c (ample N I) J)(F: Patron.Rail c (ample N I) U)
local notation "K"=> Keys c N
local notation "R"=> Spine I
local notation "b!"=> banknote N p θ
local notation "d!"=> withdraw N p θ
local notation "T!"=> Trail Y F t
namespace Stags
open Card Card.Iris
open Kit Kites ConnectedActivityE6 Pressure Sample Sample.LoomT
variable {D:I→Type}
variable (X: Reel c 6 I E) (h:X.Book p q)
local notation "E₁"=> Sigma (LoomT.Single X)
local notation "E₂"=> LoomT.LargeE X
include h
noncomputable def unMix (h:∀ i, (X.z i).Nonempty) : (Sigma (Single X) ⊕ LargeE X)≃ E:=by
   let f: E₁⊕ E₂→ E:= Sum.elim (fun i=> i.2.val) Subtype.val; refine Equiv.ofBijective f ⟨fun p q e=>?_,fun i=>?_⟩
   · have he (a:E₁): (X.z a.snd.val).card =1:=(congr_arg Finset.card a.snd.property).trans (card_singleton _) -- equality of subtype value.V may motive wrong
     have hv(a:E₁)(b:E₂) (h:a.2.val=b.val):False:=by have hh:=b.property; have h1:(X.z b.val).card=1:=h ▸ he _; omega
     rcases p with v|v <;> rcases q with q|q
     · apply congr_arg Sum.inl; change v.2.val=q.2.val at e; have hx:v.fst=q.fst:=Finset.singleton_injective (v.2.property.symm.trans ((congr_arg _ e).trans q.2.property)); rcases v,q with ⟨⟨v,u⟩,q,w⟩; change v=q at hx; subst v; exact Sigma.ext rfl (heq_of_eq (Subtype.ext e))
     · exact (hv v q e).elim
     · exact (hv q v e.symm).elim
     exact congr_arg Sum.inr (show v=q from Subtype.ext e)
   by_cases hp: 2 ≤ (X.z i).card; · exact ⟨Sum.inr (⟨i,hp⟩),rfl⟩
   have ht:=Finset.card_pos.mpr (h i); obtain ⟨a,ha⟩:= Finset.card_eq_one.mp (show (X.z i).card=1 from by omega); exact ⟨Sum.inl ⟨a,⟨i,ha⟩⟩,rfl⟩
-- Summable splits
omit h
variable (V:Grid c)
lemma sigmaTS {f:(Σ i,D i)→ EvenA c N}(hv:∀ i, Summable fun j=> ‖f (⟨i,j⟩ :Sigma D)‖) : Summable f:=(by apply Summable.of_norm; exact (summable_sigma_of_nonneg fun i=>norm_nonneg _).mpr ⟨hv,Summable.of_finite⟩) -- annot
lemma sigmaV {A:Type}[NormedAddCommGroup A][CompleteSpace A]{f:(Σ i,D i)→A}(hv:∀ i,Summable fun j=>‖f (⟨i,j⟩:Sigma D)‖): Summable f:=(by apply Summable.of_norm; exact (summable_sigma_of_nonneg fun i=> norm_nonneg _).mpr ⟨hv,Summable.of_finite⟩)
include h
-- X=P.Level.primary.Today.P.C.M
lemma gala (hv: Summable fun i=>X.mist t i V): X.rope t V=(survived X).rope t V + ∑ i:I, ∑' j:Single X i,X.mist t j.val V:=by
     let f:= fun i=> Reel.mist X t i V; let h:= h.stays; let Z:= unMix X h; let g(i:E₁):=f i.snd.val; let a:E₁⊕ E₂→ _:=f ∘ Z
     have hSum:Summable a:=Z.summable_iff.mpr hv; have hg : Summable g:= hSum.comp_injective (i:=Sum.inl) Sum.inl_injective; rw [add_comm,← (show (∑' i:I,∑' j:Single X i,X.mist t j.val V)=∑ i:I,∑' j:Single X i,X.mist t j.val V from tsum_fintype _)]; -- annot.Binding.
     unfold Reel.rope; change (∑' i,f i)=_+_; refine Eq.trans (Z.tsum_eq f|>.symm) ((HasSum.tsum_eq (hg.hasSum.sum (f:=a) (hSum.comp_injective (i:=Sum.inr) Sum.inr_injective|>.hasSum))).trans ?_); exact congr_arg₂ (·+·) hg.tsum_sigma rfl
end Stags
end YM.MassiveQCD.Plate
