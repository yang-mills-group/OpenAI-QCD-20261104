import YM.Eden.Pulpy
/-! # Approximal Taylor weighted at birth.Permit. Full roots. -/
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
local notation "markₚ"=> setas d (revere d p)
-- mini warrant transform weighted price.
variable {P:BudgetPoint}{θ t':ℝ}
local notation "F0"=>𝓝[>] (0:ℝ)
noncomputable def warpM (g s:ℕ)(t v:ℝ)(p:Mini d):Mini d:= (↑(levy g s t v):ℂ)⁻¹ • p
variable {X:Drape}{y:Mini d}
structure Horn (H:SourceRead.TaperHol)(V:Drape)(p:Mini d)(g q m:ℕ) (Z:ℝ→ Mini d):Prop where
    woke (t v:ℝ)(hp:0<v)(ht:0<t): ∃ y:Mini d, (∀ (n:Side)(o:Cover),m ≤ n.val→ Poised.Beacon.ActionTest H o (warpP g q t v V n o) y.val)∧ prism t v d y=Z t
    esteem:Tendsto Z F0 (𝓝 p)
lemma hornCost (h:Survey Q X g q y):∃ L:ℝ→Mini d,∃ K:ℕ,Horn Q X y g q K L:=by
     obtain ⟨z,⟨K,hK⟩,ht⟩:=h.grantX; let L(t:ℝ):Mini d:=(↑(t^g):ℂ)⁻¹ • PrismD.prism t 1 d z; refine ⟨L,K,?_,ht⟩; intro t v hp hθ; let x:ℂ:= (↑(levy g q t v):ℂ); refine ⟨x⁻¹ • z,fun n o hn=>constA o Q x⁻¹ _ _ (hK n o hn),?_⟩; let n:Side:=⟨K+1,Nat.succ_pos _⟩; have he:= sizedSpin (n:=n) 0 Q X z q g h.paid (fun n o U=> convoy h.paid U o) (hK n 0 (by change K≤ K+1; omega)) v t
     rw[map_smul,he,smul_smul]; congr 1; unfold x levy; rw[Complex.ofReal_mul,mul_inv, mul_assoc,← Complex.ofReal_pow,inv_mul_cancel₀ (by exact_mod_cast (pow_pos hp q).ne'),mul_one]; -- test arg
omit [Fintype I] in
lemma sumsAct (F:Finset I)(X:I→Insertion n 6)(v:I→Mini d)(o:Cover)(h:∀ i∈ F,Beacon.ActionTest Q o (X i) (v i).val) : Beacon.ActionTest Q o ⇑(∑ i∈F,X i) (∑ i∈F,v i).val:=by
    induction F using Finset.induction_on with
    | empty=> rw[sum_empty,sum_empty]; intro J; simp only [ContinuousMap.coe_zero]; change SourceRead.Agrees _ (SourceRead.desired (0: Pol d) J); rw[← funext (observe J (0:Pol d)), show Beacon.moment Q o J (0:Grid n→ Lat.Fields n 6)= (fun _=> (0:SpinPol d)) from funext fun _=>map_zero _]; simp only [map_zero]; exact ⟨contDiffAt_const,contDiffAt_const,fun _ _=>rfl⟩
    | insert i F hi ih=> rw[sum_insert hi,sum_insert hi]; exact plusA o Q _ _ _ _ (h i (mem_insert_self ..)) (ih fun i hi'=>h _ (mem_insert_of_mem hi'))
-- data.Herm.Int approximate after charge.St contour lemma two parts pricing base before-L. Bound Z-pol strongly.
local notation "TR"=> oink d g q
local notation "τ"=> P.threshold
variable (ε:ℝ)(he:0<ε)
include hp hk he
lemma book :∃ m:ℕ,∃ δ L:ℝ,0<δ∧1≤ L ∧∀ (t v:ℝ)(h:0<t)(hv:0<v),t<δ → ∀ X: Pad d→ℂ, (∑ i∈TR, ‖X i‖)*L<ε/2→ (let F:=warpP g q t v Y+∑ i∈TR,X i • warpP i.1.length i.2.length t v (wide d 1 (motto i));∃ y:Mini d,(∀ (n:Side)(o:Cover),m ≤ n.val → Beacon.ActionTest Q o (F n o) y.val) ∧ ‖PrismD.prism t v d y-setas d (revere d p)‖ < ε):=by
    let A:=TR; obtain ⟨z,M,hz⟩:= hornCost Q (chart Q K hk p hp); choose f N hf using fun (i:↥(oink d g q))=> hornCost Q (ages Q K hk i.val); let m:=M+ univ.sup N; have hl:= Metric.tendsto_nhds.mp hz.esteem (ε/2) (by positivity); let f'(x:Pad d)(s:ℝ):= if h:x∈ A then f ⟨x,h⟩ s else 0
    let L₁:= fun z: ↥(oink d g q)=> ‖setas d (revere d (motto z.val))‖+1; let L:= max 1 (∑ x,L₁ x); refine Exists.intro m (?_); have hG: (∀ᶠ i:ℝ in F0, dist (z i) markₚ< ε/2 ∧ ∀ p∈ TR, ‖f' p i‖≤ L):=by
        have ht(i:↥(oink d g q)): ∀ᶠ v:ℝ in F0, ‖f i v‖ < L₁ i:= (hf i).esteem.norm.eventually (gt_mem_nhds (lt_add_one ..))
        filter_upwards [eventually_all.mpr ht,hl] with i h he; refine ⟨he,fun v hv=> ?_⟩; unfold f'; rw[dif_pos hv]; let z :↥(oink d g q):=⟨v,hv⟩; exact (h z).le.trans ((single_le_sum (fun i _=> by unfold L₁; positivity) (mem_univ z)).trans (le_max_right ..))
    obtain ⟨δ,hδ,h⟩:= Metric.mem_nhdsWithin_iff.mp hG; refine ⟨δ,L,hδ, le_max_left ..,?_⟩; intro t v ht hv h' X hX F; let G:= fun i:Pad d=>warpP i.1.length i.2.length t v (wide d 1 (motto i)); obtain ⟨i,hi,hi'⟩:= hz.woke t v hv ht; choose X' h1 h2 using fun i:↥(oink d g q)=> (hf i).woke t v hv ht; let Y':=fun i:Pad d=> if a:i∈ TR then X i • X' ⟨i,a⟩ else 0
    refine ⟨i+ ∑ z∈A,Y' z,fun n o hn=>?_,?_⟩
    · change Beacon.ActionTest Q o (F n o) _; unfold F; simp only [Pi.add_apply, Finset.sum_apply]; refine plusA o Q _ _ _ _ (hi n o (le_trans (Nat.le_add_right ..) hn)) (sumsAct Q (oink d g q) _ Y' o (?_)); intro z hz'; unfold Y'; rw[dif_pos hz']; let a:↥(oink d g q):=⟨z,hz'⟩; exact constA o Q (X z) _ _ (h1 a n o ((Finset.le_sup (f:=N) (mem_univ a)).trans ((Nat.le_add_left ..).trans hn)))
    obtain ⟨hp,hq⟩:=h (a:=t) ⟨show t∈Metric.ball 0 δ from (by simp [Real.dist_eq,abs_of_pos ht,h']),ht⟩; change dist (z t) markₚ < ε/2 at hp; rw[dist_eq_norm] at hp; rw [map_add,map_sum,add_sub_right_comm,hi']; apply (norm_add_le ..).trans_lt; rw [← show ε/2+ε/2= ε from add_halves _]; apply add_lt_add; swap; -- rw changes hp? only RHS
    · apply (norm_sum_le ..).trans_lt; apply lt_of_le_of_lt _ hX; unfold A; rw [sum_mul]; apply sum_le_sum; intro p hp; unfold Y'; rw [dif_pos hp,map_smul,norm_smul, h2]; have hz:=hq p hp; change ‖f' p t‖ ≤ L at hz; rw[show f' p t=f ⟨p,hp⟩ t from dif_pos hp] at hz; exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    exact hp
end YM.Massive.Evo
#print axioms YM.Massive.Evo.book
