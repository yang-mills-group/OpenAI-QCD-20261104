import YM.Eden.Soda
/-! # after-L perturbation privileges.St.S hot.Abstract all cylinders, α. -/
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
open Poised.Plans RP YM.Source YM.Source.Drops QCD.Anomaly QCD.Creek Next.Fluctuations
structure Fi (C:ℝ)(j:ℕ)(z:Bard d): Prop where
     cash : 0 ≤ C
     pays {n:Side}(v:Cover)(U:Grid n)(η F M:ℝ)(hm:1 ≤ M)(hη: η*F ≤ M)(hk:0≤η)(hf:0≤F)(hg:F≤1)(hp:nob su F U): Rover (taxP d v U η z) (powerG d v U η z) (C*M^j) F
lemma fi_base : Fi 1 0 (1:Bard d):=by
     refine ⟨zero_le_one,fun {n} v U η F M hm hη hk hf hg hp=>?_⟩; let Y: Bard d:= (1:Lily su d)⊗ₜ[ℂ] (1:SpinPol d); change Rover (taxP _ _ _ _ Y) (powerG _ _ _ _ Y) _ F; unfold Y; rw[testimonP,power_t,map_one,map_one,map_one,map_one,one_smul]; constructor; swap; · rw[sub_self,norm_zero]; positivity
     simp
lemma fi_words (p:Pad d):∃ C:ℝ,Fi C p.1.length (motto p):=by
    rcases p with ⟨p,q⟩; induction p with
    | nil=> induction q with
        | nil=> exact ⟨_,fi_base⟩
        | cons i q h=>
           obtain ⟨B,hB⟩:= h; obtain ⟨C,hc,H⟩:= Epair i; refine ⟨3*C*B,mul_nonneg (by positivity) hB.cash,fun {n} v U η F M hm hη hk hf hg hp=>?_⟩; have ha:=hB.pays v U η F M hm hη hk hf hg hp; rw [compoS]; apply (spinning _ _ _ _ hg (H v U η F hf hp) (x:=1) (y:=1) (q:=Lξ q) ha).raise (?_) hf; simp
    | cons i p h=>
       obtain ⟨B,hB⟩:=h; obtain ⟨C,hc,H⟩:=Ppair i; refine ⟨3*C*B,mul_nonneg (by positivity) hB.cash,fun {n} v U η F M hm hη hk hf hg hp=>?_⟩; rw[compoG]; apply (spinning (x:=MvPolynomial.X i) _ _ _ _ hg ((H v U η F hk hf hp).raise (mul_le_mul_of_nonneg_left hη hc) hf) (y:=Lχ p) (q:=Lξ q) (hB.pays v U η F M hm hη hk hf hg hp)).raise (?_) hf; change _ ≤ _ *M^(p.length+1); rw[pow_succ']; ring_nf; rfl -- normalize countL.
variable {C B:ℝ}{X Y:Bard d}
lemma Fi.raise (h:Fi C j X)(hp: j≤ m)(hb:C ≤ B): Fi B m X:=by
     refine ⟨h.cash.trans hb,fun {n} v U η F M hm hη hk hf hg hp=> ((h.pays v U η F M hm hη hk hf hg hp).raise (?_) hf)⟩; gcongr; exact h.cash.trans hb
lemma Fi.scale (h:Fi C j X)(a:ℂ): Fi (‖a‖*C) j (a • X):=by
    refine ⟨mul_nonneg (norm_nonneg _) h.cash,fun {n} v U η F M hm hη hk hf hg hp=>?_⟩; have ht:=h.pays v U η F M hm hη hk hf hg hp; constructor
    · rw[map_smul,norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left ht.normP (norm_nonneg _)
    rw[map_smul,map_smul, ← smul_sub,norm_smul,mul_assoc,mul_assoc ‖a‖]; exact mul_le_mul_of_nonneg_left (ht.buds.trans_eq (mul_assoc ..)) (norm_nonneg _)
lemma Fi.joins (h:Fi C j X)(ht:Fi B j Y): Fi (C+B) j (X+Y):=by
    refine ⟨add_nonneg h.cash ht.cash,fun {n} v U η F M hm hη hk hf hg hp=>?_⟩; have he:= h.pays v U η F M hm hη hk hf hg hp; have hx:= ht.pays v U η F M hm hη hk hf hg hp; rw[map_add,map_add,add_mul]; constructor; · exact (norm_add_le ..).trans (add_le_add he.normP hx.normP)
    rw[add_sub_add_comm,add_mul]; exact (norm_add_le ..).trans (add_le_add he.buds hx.buds)
lemma fi_zero {j:ℕ} : Fi 0 j (0:Bard d):=by refine ⟨le_rfl,fun {n} v U η F M hm hη hk hf hg hp=>?_⟩; rw [map_zero,map_zero,zero_mul]; constructor; all_goals simp
lemma Fi.gain (S: Finset (Pad d))(A:Pad d→ Bard d)(C:Pad d→ℝ)(h:∀ i∈S,Fi (C i) j (A i)): Fi (∑ i∈S,C i) j (∑ i∈S,A i) :=by induction S using Finset.induction_on with|empty=> rw [sum_empty,sum_empty]; exact fi_zero|insert a s ha hA=> rw [sum_insert ha,sum_insert ha]; exact (h _ (mem_insert_self ..)).joins (hA (fun i hi=>h _ (mem_insert_of_mem hi)))
lemma in_flame (A:Bard d) (h:A∈Rgl d i k m): ∃ C:ℝ, Fi C k A:=by
    refine Submodule.span_induction (p:=fun x _=>∃ C:ℝ,Fi C k x) ?_ ⟨_,fi_zero⟩ (fun x y _ _ ⟨_,h⟩ ⟨_,hp⟩=>⟨_,h.joins hp⟩) (fun a x _ ⟨_,h⟩=>⟨_,h.scale a⟩) h
    rintro _ ⟨p,h,rfl⟩; obtain ⟨L,hl,hQ,hp⟩:= couP p; rw [←hp]; rw [show tagwt p = _ from h] at hl; rw[← show _=k from hl]; exact fi_words _
lemma listens (d k m:ℕ): ∃ X:ℝ,0 ≤ X ∧∀ {a:ℝ}{p:Bard d},Quota motto (raysL k m) p a→ Fi (X*a) k p:=by
    let Z:=oink d k m; choose C hc using fi_words (d:=d); let S:=∑ i∈ Z,C i; have h:0≤ S:=sum_nonneg (fun i _=>(hc i).cash); refine ⟨S,h,fun {a p} h=>?_⟩; obtain ⟨X,rfl,he⟩:=h.allot (Z:=Z) (le_of_eq (raysR d k m|>.coe_toFinset).symm); apply Fi.raise (Fi.gain Z (fun x=>X x • motto x) (fun i=>‖X i‖*S) (?_)) le_rfl (?_)
    · intro i hi; have hb:i∈ raysL k m:=(raysR d k m|>.mem_toFinset).mp hi; exact ((hc i).raise hb.1 (single_le_sum (fun i _=>(hc i).cash) hi)).scale _
    rw [← sum_mul]; rw[mul_comm S]; exact mul_le_mul_of_nonneg_right he (sum_nonneg fun i _=>(hc i).cash)
-- output on full Self.Tapes.Unscaled η. robustness for any ≤ cloth. costs fixed H.F etc AFTER L. suffices SVal injection logic
lemma stances (p:Bard d)(h:p∈ Rgl d i k m)(C:ℝ)(hz:0≤C) : ∃ A:ℝ,0 ≤ A ∧∀ {c:Side} {u:ℕ}(H:Bed)(F:Train u)(ht:(milky 0 H c (G:=su) (d':=d)).IsSymm), Farm (wager 0 H c ht) (corsage F c d 0) C→∀ W:ℝ,0 ≤ W→ Fi ((W^i)*A) k (reelW d H c F ht (padU d W p)):=by
    obtain ⟨T,hT,HV⟩:= pledgesN C hz p h; obtain ⟨X,hX,H⟩:=listens d k m; obtain ⟨B,hB⟩:=in_flame p h; refine ⟨X*T+B,add_nonneg (mul_nonneg hX hT) hB.cash,fun {c u} R F ht hp W hv=>?_⟩; have he:= H (HV _ _ hp); rw [rates W p h, map_smul, ←Real.norm_of_nonneg (pow_nonneg hv i), ←Complex.norm_real,Complex.ofReal_pow]; apply Fi.scale; have hY := he.joins hB; rw [sub_add_cancel] at hY; exact hY -- remove V
end YM.Eden
#print axioms YM.Eden.stances
