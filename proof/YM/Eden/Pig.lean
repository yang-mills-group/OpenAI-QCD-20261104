import YM.Eden.Garnish
/-! # lower sleeves, projection-birth priors.Was with true self normal -/
set_option autoImplicit false
noncomputable section
namespace YM.Eden
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior
open Finset Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free Bloom Arise Arise.Range Bloom.TreeP
open scoped Topology BigOperators InnerProductSpace Matrix Matrix.Norms.Frobenius TensorProduct Classical
variable {G:Gauge}{d k i m j:ℕ}{c f n:Side} {H:Bed}{t:Clip}{a b:ℝ}{I J :Type}[Fintype I][Fintype J]
open Massive UV QCD QCD.Eden QCD.Grass QCD.Bloom Lat Poised.Display
open Elm Elm.SparK Elm.SparK.Arbor Elm.SparK.Arbor.PrismD Poised Papyrus Lining Next.Rank.Normal Cylinder
open Poised.Plans RP YM.Source YM.Source.Drops QCD.Anomaly QCD.Creek
abbrev Lp (d:ℕ):= List (Tube su d)
abbrev Lq (d:ℕ):= List (Sings d)
abbrev Pad (d:ℕ):= Lp d × Lq d
noncomputable def motto (U:Pad d):Bard d:= (U.1.map MvPolynomial.X).prod⊗ₜ[ℂ](U.2.map Grass.atom).prod
-- Finitely bounded combination of downward words. Preserve below seminorm for permit. Abstract.Type
section
variable {A B T V:Type*}[AddCommGroup T][Module ℂ T][AddCommGroup V][Module ℂ V]
noncomputable def Quota (D: A→T)(S:Set A)(z:T)(v:ℝ):Prop:=∃ (Y:Finset A)(u:A→ℂ),(Y:Set A)⊆ S ∧ z=∑ i∈Y,u i • D i ∧ ∑ i∈Y, ‖u i‖ ≤ v
variable (P:A→ T)
lemma sterile {S:Set A}{v:ℝ}(h:0 ≤ v): Quota P S 0 v:=by refine ⟨∅,0,?_,?_,?_⟩ <;> simp [h]
lemma ticksY{S:Set A}{i:A}(h:i∈S): Quota P S (P i) 1:= ⟨{i},fun _=>1,by simpa,by simp,by simp⟩
variable {P}{Q:B→V}{x y:T}{s t C:ℝ}{R S:Set A}
lemma Quota.mono(h:Quota P R x s)(ht:R⊆ S)(hc:s≤ t): Quota P S x t:=by obtain ⟨i,j,ha,hv,hj⟩:=h; exact ⟨_,_,ha.trans ht,hv,hj.trans hc⟩
lemma Quota.fare(h:Quota P R x s):0 ≤ s:=by obtain ⟨i,j,ha,hv,hj⟩:=h; exact (sum_nonneg (fun _ _=>norm_nonneg _)).trans hj
lemma Quota.allot {Z: Finset A}(hS:S⊆ (Z:Set A))(h:Quota P S x s) :∃ u:A→ ℂ,x=∑ i∈ Z,u i • P i ∧ ∑ i∈ Z, ‖u i‖ ≤ s:=by
    obtain ⟨i,j,ha,hv,hj⟩:=h; let k(a:A):ℂ:= if a∈i then j a else 0; have ht: i⊆ Z:= Finset.coe_subset.mp (ha.trans hS); refine ⟨k,?_,?_⟩
    · rw [← sum_subset ht (f:=fun i=>k i • P i) (fun _ _ h=>by simp [k,h]),hv]; exact sum_congr rfl fun v h=>by simp [k,h]
    rw [← sum_subset ht (f:=fun i=>‖k i‖) (fun _ _ h=>by simp[k,h])]; exact le_trans (sum_le_sum fun i h=> by rw[show k i= _ from if_pos h]) hj
lemma Quota.joins (h:Quota P S x s)(ht:Quota P S y t):Quota P S (x+y) (s+t):=by
    obtain ⟨i,j,h1,h2,h3⟩:= h; obtain ⟨a,b,h4,h5,h6⟩:=ht; let W:= i∪ a; obtain ⟨u,hu,U⟩:= Quota.allot (P:=P) (Z:=W) (S:=(i:Set A)) (by simp [W]) (show Quota P (i:Set A) x s from ⟨_,j,Set.Subset.refl _,h2,h3⟩); obtain ⟨v,hv,V'⟩:=Quota.allot (P:=P) (Z:=W) (S:=(a:Set A)) (by simp [W]) (show Quota P (a:Set A) y t from ⟨_,b,Set.Subset.refl _,h5,h6⟩)
    refine ⟨W,fun a=>u a+v a,?_,?_,?_⟩; · simpa only [W,Finset.coe_union,Set.union_subset_iff] using And.intro h1 h4
    · simp_rw [add_smul,sum_add_distrib,←hu,←hv]
    exact le_trans (sum_le_sum fun i _=> norm_add_le ..) (by rw [sum_add_distrib]; exact add_le_add U V')
lemma Quota.sums(F:Finset B)(K:B→T)(t:B→ℝ)(h:∀ i∈F,Quota P S (K i) (t i)): Quota P S (∑ i∈F,K i) (∑ i∈F,t i):=by induction F using Finset.induction_on with |empty=> rw[sum_empty,sum_empty]; exact sterile P le_rfl|insert i F hi ih=>rw[sum_insert hi,sum_insert hi]; exact (h _ (mem_insert_self ..)).joins (ih fun i hi'=>h i (mem_insert_of_mem hi')) -- Finset Decidable issue classical self
lemma Quota.scale(h:Quota P S x s)(t:ℂ): Quota P S (t • x) (‖t‖ * s):=by
    obtain ⟨i,j,h1,h2,h3⟩:=h; refine ⟨i,fun x=>t*j x,h1, ?_,?_⟩; · simp_rw[mul_smul,← smul_sum, ← h2]
    simp_rw [norm_mul, ←mul_sum]; exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
lemma Quota.down {W:Set B}(h:Quota P S x s)(f:T→ₗ[ℂ] V)(t:A→B)(hw: Set.MapsTo t S W)(hg:∀ i∈S, f (P i)=Q (t i)): Quota Q W (f x) s:=by
    obtain ⟨i,j,h1,h2,h3⟩:=h; rw [h2,map_sum]; refine (Quota.sums i _ (fun k=> ‖j k‖*1) fun k he=> ?_).mono (Set.Subset.refl W) ?_
    · rw [map_smul,hg k (h1 he)]; exact (ticksY Q (hw (h1 he))).scale (j k)
    simpa only [mul_one] using h3
end
variable {Gg: Symmetric (Tube su d)}{Sp:Matrix (Sings d) (Sings d) ℂ}(u: Tube su d)(v:Sings d)
set_option quotPrecheck false
local notation "V"=>TensorProduct.map (milk Gg) (QCD.Creek.birth (Wand Sp)).toLinearMap
local notation "Σ₇"=> List (Tube su d)
noncomputable abbrev Lχ (P:Lp d): Lily su d:=(P.map MvPolynomial.X).prod
noncomputable abbrev Lξ(P:Lq d): SpinPol d:=(P.map Grass.atom).prod
noncomputable abbrev Gχ (p:Tube su d): Bard d:= MvPolynomial.X p⊗ₜ[ℂ]1
noncomputable abbrev Gξ(p:Sings d): Bard d:= (1:Lily su d)⊗ₜ[ℂ] Grass.atom p
variable (p:Lp d)(q:Lq d)
lemma compoG :motto (u::p,q)=Gχ u*motto (p,q):=by unfold motto Gχ; rw[Algebra.TensorProduct.tmul_mul_tmul,one_mul]; rfl
lemma compoS : motto ([],v::q)=Gξ v*motto ([],q):=by unfold motto Gξ; rw[Algebra.TensorProduct.tmul_mul_tmul,one_mul]; rfl
lemma slitE (u:Tube su d)(P: Lp d): slit (Gg.cov u) (Lχ P)= ∑ i:Fin P.length, (Gg.cov u (P.get i)) • Lχ (P.eraseIdx i.val):=by
     induction P with
     | nil=> rw [show Lχ []=(1:Lily su d) from rfl, Derivation.map_one_eq_zero]; simp
     | cons k p ih=> let f(i:Fin (p.length+1)):= (Gg.cov u ((k::p).get i)) • Lχ ((k::p).eraseIdx i.val); change _=∑ i,f i; rw[show Lχ (k::p)=MvPolynomial.X k*Lχ p from rfl, slit_prod,ih, Fin.sum_univ_succ f]; unfold f; simp only [Fin.val_zero,Fin.val_succ,List.length_cons,List.eraseIdx_cons_succ,List.eraseIdx_zero,List.get_cons_succ,List.get_cons_zero]; rw [mul_sum,add_comm,MvPolynomial.C_mul']; congr 1; exact sum_congr rfl fun i _=> _root_.mul_smul_comm ..
-- exact step on all symbol.Matrix.Combined
lemma attestG : V (motto (u::p,q))=Gχ u * V (motto (p,q))+∑ i:Fin p.length, (Gg.cov u (p.get i)) • V (motto (p.eraseIdx i.val,q)):=by
    unfold motto; simp_rw [TensorProduct.map_tmul]; change milk Gg (MvPolynomial.X u*Lχ p)⊗ₜ[ℂ]_=_; rw [feeds,skims,slitE,map_sum, TensorProduct.add_tmul,TensorProduct.sum_tmul, Gχ,Algebra.TensorProduct.tmul_mul_tmul,one_mul]; exact congr_arg₂ _ rfl (sum_congr rfl fun i _=>by rw[map_smul, ← TensorProduct.smul_tmul'])
noncomputable def dollars(Sp:Matrix (Sings d) (Sings d) ℂ) (v:Sings d)(q: Lq d) (i:Fin q.length):= (-1:ℂ)^i.val*(Sp v (q.get i)-Sp (q.get i) v)
lemma attestS : V (motto ([],v::q)) = Gξ v* V (motto ([],q)) + ∑ i:Fin q.length, dollars Sp v q i • V (motto ([],q.eraseIdx i.val)) :=by
    unfold motto; simp_rw[TensorProduct.map_tmul]; change milk Gg (1:Lily su d) ⊗ₜ[ℂ] Creek.birth (Wand Sp) (atom v * Lξ q) = _; rw [Arise.Pair.ravels, Arise.Pair.gathers,map_sum,TensorProduct.tmul_add, TensorProduct.tmul_sum, Gξ, Algebra.TensorProduct.tmul_mul_tmul,one_mul]; refine congr_arg₂ _ rfl (sum_congr rfl (fun i _=>?_)); rw [map_smul,TensorProduct.tmul_smul]; rfl
end YM.Eden
#print axioms YM.Eden.attestS
#print axioms YM.Eden.attestG
