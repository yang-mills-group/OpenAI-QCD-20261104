import YM.Play.Sam
import YM.Play.Bonnet
import YM.Play.Cot
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Play
open QCD Function MeasureTheory Filter Finset QCD.Grass QCD.Cove Matrix QCD.Beam QCD.Beam.Pipe Bera Anomaly
open scoped Topology ContDiff BigOperators Classical Matrix InnerProductSpace NNReal ENNReal
variable {A B:Type*}[MeasurableSpace A][MeasurableSpace B]{D E U V:Type}[Fintype D][Fintype E][Fintype U][Fintype V]{κ:Measure A}{μ:Measure B} [IsProbabilityMeasure μ][IsProbabilityMeasure κ]
variable {a u' d s c t q v σ β η r k:ℝ}{S:Set B}{N:Finset D}{W: Finset E}{X:Finset U}{n m:ℕ}
open Oce
section
variable (hP: Papers D (Patio U))(L:Patio U →ₗ[ℂ] Patio V)(f:A×B→ Patio V)
variable (P:Matrix D E ℂ){Q':Next.Rank.Normal.Symmetric D}{w:B→ D→ℝ}{u:D→ℝ}(hp:Corolla μ w u Q') (b:E→ℝ)
include hp
-- average price
lemma fels (ht: hP∈Ledger X N n m)(hh: Pane Q' N t) (hu:0 ≤ t) (he:bill u N r)(hr:1 ≤ r)(hk:0<k)(hU:∀ i,(u i:ℂ)=∑ j,P i j*(b j:ℂ))(h:Integrable f (κ.prod μ))
   (hc: MeasurableSet S) (hZ:∀ i,i.2∉S→ ‖f i‖ ≤ a)(hY:∀ i,i.2∈S → ‖f i - L (rose U (w i.2) hP)‖ ≤ η)(hn:0 ≤ a)(hd:0 ≤ η)(hM:μ.real Sᶜ ≤ v)(hs:∀ x: Patio U,x.val∈ Rim X m → ‖L x‖ ≤ d*‖x‖):
   ‖(∫ z,f z ∂ κ.prod μ)-rose V b (Bera.ferry (Next.Rank.Normal.pipe (spool P) Q') L hP)‖ ≤ η + (v*a+(v*k+k⁻¹*expat n r t)*(d*cents hP)):=by
     rw [← comingV hp P L hP b hU] -- order
     exact petite h (offering hp L hP) hc hZ hY hM (joins hp L hP ht hs hh hu he hr hk _ hM) hd hn
end
variable (hP: Papers D (Patio U))(P:Matrix D E ℂ)(Q R:Next.Rank.Normal.Symmetric D)(M:Matrix U V ℂ)(K:Matrix U U ℂ)
-- true price from alternative gauge.He
lemma kur (ht: hP∈ Ledger X N n m) (he:Sky P Q M K N X s u' t q) (h: Sky P R M K N X s u' t q)(hv: drifts P Q M K P R M K N X β)(hβ:0 ≤ β)(hp:∀ i∈N,∀ j,P i j≠0→j∈W)(b:E→ℝ) (hw:bill b W r)(hr:1 ≤ r):
    ‖rose V b (shootsW P Q M K hP)-rose V b (shootsW P R M K hP)‖ ≤ r^n*(windfall s u' t q n m*β*cents hP):=by
       have h0:shootsW P Q M K hP-shootsW P R M K hP∈Ledger (Finset.univ) W n m:= Submodule.sub_mem _ (types P Q M K ht hp (fun _ _ _ _=> mem_univ _)) (types _ _ _ _ ht hp (fun _ _ _ _=> mem_univ _))
       rw [← map_sub]; exact (cares h0.2 hw hr).trans (mul_le_mul_of_nonneg_left (momentQ P Q M K P R M K hP ht he h hβ hv) (pow_nonneg (zero_le_one.trans hr) _))
-- comparison error in actual step. assume L,L' quantitative.Shop.W. Use ℓ1 weights norm. Provide lens.E.
omit [Fintype E]
lemma jagged (x:Patio U)(p: Patio U →ₗ[ℂ] Patio V)(g: Patio U →ₗ[ℂ] Patio V) (b c : D→ℝ) (ht:hP∈Ledger X N n m)(he: x∈ vaultS X m)(hx: ‖x-rose U b hP‖ ≤ η) (hb:bill b N r)(hc:bill c N r)(h:∀ i∈N,‖b i-c i‖ ≤ σ)(hr:1 ≤ r)(hD:0 ≤ d)(hd:0 ≤ q)(hv:0 ≤ σ) (hf:∀ y∈ vaultS X m,‖(p y)‖ ≤ d*‖y‖)(hy:∀ y∈vaultS X m,‖p y-g y‖ ≤ q*‖y‖) :
   ‖p x-g (rose U c hP)‖ ≤ d*(η + n*σ*r^n*cents hP) + q*(r^n*cents hP):=by
    let y:=rose U c hP; let z:= rose U b hP; have hz:y∈vaultS X m:=passage c ht.1
    have ht': ‖x-y‖ ≤ η+n*σ*r^n*cents hP:= (norm_sub_le_norm_sub_add_norm_sub x z y).trans (add_le_add hx (tang b c hP ht.2 hb hc hr h hv))
    refine (norm_sub_le_norm_sub_add_norm_sub (p x) (p y) (g y)).trans (add_le_add (?_) (?_)); · rw [←map_sub]; exact (hf _ (Submodule.sub_mem _ he hz)).trans (mul_le_mul_of_nonneg_left ht' hD)
    exact (hy _ hz).trans (mul_le_mul_of_nonneg_left (cares ht.2 hc hr) hd)
end YM.MassiveQCD.Play
#print axioms YM.MassiveQCD.Play.jagged
#print axioms YM.MassiveQCD.Play.fels
