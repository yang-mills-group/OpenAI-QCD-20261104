import YM.Helio.Fable
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
variable {Γ:Silo c}{A: BankP c}{U:St c}
namespace Meridian
structure ParcelZ {c:Side} where
   (α β : Site c)
   R : Support c
   f : Grid c→Bundle
namespace ParcelZ
variable (d:ParcelZ (c:=c))
def val : St c:= fun V=> Stew.block d.α d.β (d.f V)
structure Ticket (p:BudgetPoint)(T K:ℝ)(B:ℕ):Prop where
   site : d.α∈d.R
   son : d.β∈ d.R
   tk : 0 ≤ T
   nt : 0 ≤ K
   reach : LocalOn d.R d.f
   pores : Continuous d.f
   chart (n:ℕ)(U:Grid c): Push.Local.Chart n d.f U
   con (g:Frame c)(V:Grid c): d.f (Lattice.gauge g V)=touch (colour (g d.α))*d.f V*star (touch (colour (g d.β)))
   shine : d.f 1=0
   global (V:Grid c): ‖d.f V‖*(1+(diameterQ B d.R:ℝ))^2≤ T
   mask (o:Site c)(ht:o∈d.R)(V:Grid c)(hz:Healthy p.threshold d.R V)(l:List (Directions su c))(hq:l.length ≤ p.order)(hp:∀ i∈l,p.dirBound o i): ‖leftDerivs d.f l V‖ * (1+(diameterQ B d.R:ℝ))^2 ≤ K
noncomputable def turnover: ParcelZ (c:=c):=⟨d.β,d.α,d.R,fun U=>clap (d.f U)⟩
noncomputable def rents (s:ℝ): ParcelZ (c:=c):=⟨d.α,d.β,d.R,fun U=>s • d.f U⟩
lemma returnsT : d.turnover.val = flipL ∘ d.val:=by funext V; exact (scaleF ..).symm
lemma earnsT (s:ℝ): (d.rents s).val=s • d.val:=by funext V; exact ((blockL d.α d.β).restrictScalars ℝ).map_smul ..
variable {T K:ℝ} (h:d.Ticket p T K B)
include h
lemma turnA : (turnover d).Ticket p (‖clapL‖*T) (‖clapL‖*K) B:=by
    let w:= d.turnover; have hw:w.f=clapL ∘ d.f:=rfl
    refine ⟨h.son,h.site,mul_nonneg (norm_nonneg clapL) h.tk,mul_nonneg (norm_nonneg clapL) h.nt,fun i j hv=>congr_arg clapL (h.reach i j hv),clapL.continuous.comp h.pores, fun n U=>clapL.contDiff.contDiffAt.comp _ (h.chart n _),fun _ _=>?_ ,(congr_arg clapL h.shine).trans (map_zero _),fun V=> ?_,fun o hv V hz l hn hq=>?_⟩ -- syntax
    · change clap (d.f (gauge _ _))=_; rw [h.con,pigments]; rfl
    · let D:ℝ:= diameterQ B d.R; exact (mul_le_mul_of_nonneg_right (clapL.le_opNorm (d.f V)) (show 0≤ (1+D)^2 from sq_nonneg _)).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (h.global V) (norm_nonneg clapL)) -- d.R
    rw [show d.turnover.f=_ from hw,left_linear clapL l (h.chart _ V) hn]; let D:ℝ:= diameterQ B d.R; apply (mul_le_mul_of_nonneg_right (clapL.le_opNorm _) (show 0 ≤ (1+D)^2 from sq_nonneg _)).trans; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (h.mask o hv V hz l hn hq) (norm_nonneg clapL)
lemma rentA (s:ℝ) : (rents d s).Ticket p (‖s‖*T) (‖s‖*K) B:=by
    let X: Bundle→L[ℝ]Bundle:= s • ContinuousLinearMap.id ℝ _
    let Y U:= (d.rents s).f U; have hp' :Y=X ∘ d.f:=rfl
    refine ⟨h.site,h.son,mul_nonneg (abs_nonneg s) h.tk,mul_nonneg (abs_nonneg s) h.nt,fun i j hv=>congr_arg X (h.reach i j hv),X.continuous.comp h.pores, fun n U=> X.contDiff.contDiffAt.comp _ (h.chart n U),fun _ _=> ?_, (congr_arg X h.shine).trans (map_zero _),fun V=> ?_,fun o hv V hz l hn hq=> ?_⟩
    · change s • _=_; unfold rents; simp only; rw [h.con,Matrix.mul_smul,Matrix.smul_mul] -- step adjust expansions
    · change ‖s • d.f V‖*_≤_; rw [norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left (h.global V) (norm_nonneg s)
    change ‖leftDerivs (X ∘ d.f) _ _‖ * _ ≤ _; rw [left_linear X l (h.chart _ V) hn,show X _=s • _ from rfl,norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left (h.mask o hv V hz l hn hq) (norm_nonneg s)
end ParcelZ
end Meridian
end YM.QCD.Entr
#print axioms YM.QCD.Entr.Meridian.ParcelZ.rentA
