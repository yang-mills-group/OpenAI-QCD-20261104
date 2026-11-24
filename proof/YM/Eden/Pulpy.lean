import YM.Eden.Priced
/-! # single tile budget vector.Beat.Boot scaled genuine parity widths. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Evo
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior
open Finset Filter Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free YM.Bloom YM.Arise YM.Arise.Range Bloom.TreeP
open scoped Topology BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator TensorProduct Classical
variable {G:Gauge}{d k i m j l w r g q N:ℕ}{c f n:Side} {H:Bed}{t:Clip}{a b:ℝ}{I J :Type}[Fintype I][Fintype J]
open Massive UV QCD QCD.Eden QCD.Grass QCD.Cove Lat Poised.Display
open Elm Elm.SparK Elm.SparK.Arbor Elm.SparK.Arbor.Gallery Elm.SparK.Arbor.PrismD Poised Papyrus Lining
open Poised.Plans RP YM.Source YM.Source.Drops QCD.Anomaly QCD.Creek YM.Eden Girdle Sieve Counting Counting.Terrain Pipes Facets Orientation MassiveQCD.Plate Carte.Hem Permit
variable (p:Bard d)(Q:SourceRead.TaperHol)(K:Hol su)(hk:Drops.Peg K (d/2))(hp:p∈ Rgl d i g q)
local notation "Y"=> wide d 1 p
local notation "Wt"=>oink d g q
local notation "D"=> wide d 1 ∘ motto
-- table cash for all cylinders beforeL
include hp hk Q
lemma offersL :∃ Z:ℝ,0≤ Z ∧ ∀ᶠ r:ℕ in atTop,∀ k m i j:ℕ,∃ C:ℝ,1≤ C ∧ Coin r k m i j Y g q C Z ∧∀ z∈ Wt,Coin r k m i j (wide d 1 (motto z)) z.1.length z.2.length C Z:=by
     obtain ⟨X,hX,L⟩:= merchant (chart Q K hk p hp); choose Z hz H using fun z:↥(oink d g q)=> merchant (ages Q K hk z.val)
     let V:=∑ i,Z i; have h:0 ≤ V:=sum_nonneg (fun i _=> hz i); refine ⟨max V X, h.trans (le_max_left ..),?_⟩; filter_upwards [eventually_all.mpr H,L] with r hr hu k m i j; choose A ha H using fun z:↥(oink d g q)=> hr z k m i j; let C:= ∑ i,A i; have hC:0≤ C:=sum_nonneg (fun i _=> ha i); obtain ⟨c,hc,h⟩:= hu k m i j; have he:1 ≤ C+c+1:=by linarith
     refine ⟨C+c+1,he,h.raise (by linarith) (le_max_right ..),?_⟩; intro z hp; let v:↥(oink d g q):=⟨z,hp⟩; exact (H v).raise ((single_le_sum (fun i _=>ha i) (mem_univ v)).trans (show C≤ C+c+1 from by linarith)) ((single_le_sum (fun i _=>hz i) (mem_univ v)).trans (show V ≤ _ from le_max_left ..))
-- combine for budgets after.M measure condition minimum purchases
omit hk hp Q
variable (P:BudgetPoint)(b:Cover)(θ:ℝ)
structure Priced (X:Insertion c 6)(P:BudgetPoint)(b:Cover)(r k m:ℕ)(θ t v:ℝ) : Prop where
   Fl : Flame X P (pot (r+1) c b) (wrap c b) θ k m t
   pay U : Creek.load (fun _=> θ) (X U) ≤ v
section
variable {P b θ}{X:Insertion c 6}{s t v w₀:ℝ}
lemma Priced.nothing(hs:0≤ s)(ht:0≤ t): Priced (0:Insertion c 6) P b r k m θ s t:= ⟨leFlame (flare_zero ..) _ hs, fun U=>by change Creek.load (fun _=>θ) 0 ≤ _; unfold Creek.load Creek.wscale; simpa using ht⟩
lemma Priced.shelter {Y':Insertion c 6}(h:Priced X P b r k m θ s v)(hq:Priced Y' P b r k m θ t w₀)(hθ:0 ≤ θ):Priced (X+Y') P b r k m θ (s+t) (v+w₀):=⟨flare_add _ _ X Y' h.Fl hq.Fl hθ, fun U=>(Stamp.floss_add θ ⇑X ⇑Y' _).trans (add_le_add (h.pay U) (hq.pay U))⟩
lemma Priced.raise (h:Priced X P b r k m θ s v)(ht:s≤t)(hv:v ≤ w₀): Priced X P b r k m θ t w₀:=⟨leFlame h.Fl _ ht,fun U=>(h.pay U).trans hv⟩
lemma Priced.plenty (h:Priced X P b r k m θ s v)(u:ℂ) : Priced (u • X) P b r k m θ (‖u‖*s) (‖u‖*v):=⟨flare_by _ _ X h.Fl u, fun U=>by rw [ContinuousMap.smul_apply,Creek.load_scale]; exact mul_le_mul_of_nonneg_left (h.pay U) (norm_nonneg _)⟩ -- order
lemma Priced.gaze (t:Finset (Pad d))(hX:Pad d→Insertion c 6)(s v:Pad d→ℝ)(h:∀ i∈ t,Priced (hX i) P b r k m θ (s i) (v i))(hθ:0 ≤ θ):Priced (∑ i∈t,hX i) P b r k m θ (∑ i∈t,s i) (∑ i∈ t,v i):=by induction t using Finset.induction_on with|empty=> rw[sum_empty,sum_empty,sum_empty]; exact Priced.nothing le_rfl le_rfl|insert i t hi ih=> rw[sum_insert hi,sum_insert hi,sum_insert hi]; exact (h i (mem_insert_self ..)).shelter (ih (fun i hi=>h _ (mem_insert_of_mem hi))) hθ -- `[classical]`
end
local notation "τ"=> P.threshold
variable {P b θ}{t':ℝ}{X:Drape}{C Z:ℝ}
variable (hθ:0<θ)(ht:τ ≤1)
include hθ
lemma coinW(b:Cover) (h:Coin r k m i j X g q C Z)(hk:P.order=k)(hm:P.power=m)(hs:2*(r+1)<c.val) : Priced ((warpP g q τ θ X) c b) P b r i j θ C (Z*(τ^g)⁻¹):=by
    have hp:=P.threshold_pos; have hV:0<levy g q τ θ:=by unfold levy; positivity
    let V:=(levy g q τ θ:ℂ); have he: Priced (X c b) P b r i j θ (C*levy g q τ θ) (θ^q*Z):= ⟨h.H P c b θ hθ hm hk hs, h.K c b θ hθ⟩; have hX:= he.plenty V⁻¹; unfold V at hX; rw[norm_inv,Complex.norm_real,Real.norm_of_nonneg hV.le,mul_left_comm (_⁻¹:ℝ), inv_mul_cancel₀ hV.ne',mul_one] at hX; apply hX.raise le_rfl; unfold levy; field_simp <;> first| ring|aesop
lemma coinΦ (b:Cover){j':ℕ}(R:Pad d→ℂ)(hq:∀ z∈ Wt, Coin r k m i j' (D z) z.1.length z.2.length C Z)(hv:0≤ Z)(ha:0≤ C)(hr:∑ i∈Wt, ‖R i‖ ≤1)(hk:P.order=k)(hm:P.power=m)(hs:2*(r+1)<c.val)(ht:τ ≤1) : Priced (∑ i∈ Wt,R i • (warpP i.1.length i.2.length τ θ (wide d 1 (motto i))) c b) P b r i j' θ C (Z*(τ^g)⁻¹):=by
    let T:=oink d g q; let V:=Z*(τ^g)⁻¹; have ht':= P.threshold_pos; have hx:0≤ V:=by unfold V; positivity
    let G(i:Pad d):= D i; let B(i:Pad d):= R i • (warpP i.1.length i.2.length τ θ (G i)) c b
    refine (Priced.gaze T B (fun i=>‖R i‖*C) (fun i=>‖R i‖*V) ?_ hθ.le).raise ?_ ?_
    · intro i hi; have h:i∈raysL g q:= (raysR d g q|>.mem_toFinset).mp hi; apply (Priced.raise (coinW hθ b (hq i hi) hk hm hs) le_rfl ?_).plenty (R i); unfold V; refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) hv; exact pow_le_pow_of_le_one ht'.le ht h.1 
    · rw [← sum_mul]; exact mul_le_of_le_one_left ha hr
    rw[← sum_mul]; exact mul_le_of_le_one_left hx hr
end YM.Massive.Evo
#print axioms YM.Massive.Evo.coinΦ
#print axioms YM.Massive.Evo.offersL
