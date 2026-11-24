import YM.QCD.Ruby.Sail
/-! # specialization exponentiation. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Ruby
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open Trees ConnectedActivityE6 Jets.Touch Pressure
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ}
variable {t:ℝ} {ι β ρ:Type}{a u v w A R m k σ B' v' ht q':ℝ} {B:ℕ}
variable (Y:Hue c N ι) (X:Rail c N β)
variable {p :ι→ℝ} {q:β→ℝ}
lemma hearts (hp:Y.Tall t)(he: Ac.Hit Y.bud B p a A) (ht: 0≤p)(hv:1≤v)(ha: 0≤a)(hx:∀ i U, ‖token c N v (Y.mean i U)‖ ≤ p i) (U:Grid c): Summable (fun i=>Y.mean i U) ∧ Summable (fun i=> ‖sparkY Y U i‖):=by
    let q i:= if (Y.bud i).Nonempty then p i else 0; have hq :0≤ q:=fun i=> ite_nonneg (ht i) le_rfl
    have hh : Ac.Hit Y.bud B q a A:=by
       intro x; convert! he x using 1; funext i; split
       next hx=> rw [show q i=p i from if_pos ⟨_,hx⟩]
       next _=> rfl
    have he' : Summable q:= Loom.fishes _ _ hh hq ha (fun i hv=>by_contra (fun p=>hv (if_neg p)))
    have hQ i: ‖token c N v (Y.mean i U)‖ ≤ q i:=by
       unfold q; split; · exact hx i U
       next h=> rw [show Y.mean i U=0 from ?_,map_zero,norm_zero]; exact by_contra fun hh'=> let j:=not_disjoint_iff.mp (hp.non i U hh'); h ⟨j.choose,j.choose_spec.1⟩
    refine ⟨Summable.of_norm_bounded he' (fun i=> (Loom.tore _ hv).trans (hQ _)), ?_⟩
    let Q:=∑' i,q i
    refine (he'.mul_left (Real.exp Q)).of_nonneg_of_le (fun i=> norm_nonneg _) (fun i=>?_)
    have hm:=bought _ _ _ (hQ i); apply ((tore _ hv).trans hm).trans
    have hk:= exploded (q i) 1 (hq i) le_rfl; simp only [mul_one] at hk; rw [mul_comm (Real.exp Q)]; exact hk.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (he'.le_tsum i (fun i _=>hq i))) (hq i))
def HJoin (Y:Hue c N ι)(P:Hue c N ρ):Hue c N (ι⊕ρ):=⟨Sum.elim Y.bud P.bud, Sum.elim Y.mean P.mean⟩
lemma nestling (Z:Hue c N ρ)(hh:Y.Garish)(he:Z.Garish): (HJoin Y Z).Garish:=by
    refine ⟨?_,?_,?_,?_⟩
    · rintro (i|i); exact hh.gauge i; exact he.gauge i
    · rintro (i|i); exact hh.real i; exact he.real i
    · rintro (i|i); exact hh.number i; exact he.number i
    intro s k g h; obtain ⟨d,hf,hv⟩:= hh.travel _ _ _ h; obtain ⟨f,hF,hX⟩:= he.travel _ _ _ h
    exact ⟨Equiv.sumCongr d f, (fun i=> by rcases i with i|i; exact hf i; exact hF i), fun i U=> by rcases i with i|i; exact hv i _; exact hX i _⟩
lemma branche (Z:Hue c N ρ)(hh:Y.Tall t)(he:Z.Tall t): (HJoin Y Z).Tall t:=by
    refine ⟨?_,?_,?_,?_⟩ <;> rintro (i|i) <;> first| exact hh.bond i| exact he.bond i| exact hh.meas i | exact he.meas i| exact hh.non i| exact he.non i| exact hh.lives i| exact he.lives i
-- sym CopyP assembly soft from individual Soft not rotated. similar
noncomputable def HGrace (Y: Hue c N ι): Hue c N (ManyA c ι):= ⟨fun i=> (Y.bud i.2).image (act i.1), fun i U=> averageC c • spice i.1 (Y.mean i.2 (sky i.1 U)) ⟩
lemma rak (h:Y.Tall t):(HGrace Y).Tall t:=by
    constructor <;> rintro ⟨s,i⟩
    · exact fun U V hv hh=> congr_arg (averageC c • ·) (congr_arg (spice s) (uses_pull (h.bond i) s.1 s.2 U V hv hh))
    · exact measurable_const.smul ((phare _).measurable.comp ((h.meas i).comp (continuous_pull ..).measurable))
    · intro U hn hh; apply hn; have hf : Healthy t (Y.bud i) (sky s U):=(healthy_pull ..).1 hh; change averageC c • spice s (Y.mean i (sky s U))=_; rw [show Y.mean i _=0 from by_contra fun hh=>h.non _ _ hh hf,map_zero,smul_zero] -- hc
    intro U; exact Territory.club _ _ _ (gateS s _ _ _ _ (h.lives i _))
lemma votes (hh:∀ i,shadeG (Y.mean i))(ht:∀ i U,Fit (Y.mean i U))(he:∀ i U,Regal _ _ (Y.mean i U)=Y.mean i U): (HGrace Y).Garish:=by
    constructor
    · rintro ⟨v,i⟩ U k
      suffices he : sways (Lat.rotates N k) ((HGrace Y).mean (v,i) (gauge k U))=(HGrace Y).mean (v,i) U by exact congr_arg Subtype.val he
      let P:= spice v (N:=N); change sways _ (averageC c • _) = averageC c • _; rw [eSM _ (phare _),show sky v (gauge k U)=gauge (k ∘ act v) (sky v U) from pull_gauge ..]; apply congr_arg; unfold spice
      rw [custodial k _ (assured v)]; apply congr_arg; exact Subtype.ext (hh i (sky v U) (k ∘ act v))
    · rintro ⟨s,i⟩ U; apply Patron.dolled; exact (gammaT _ (ht i _) (assured s)).trans (congr_arg _ (he i _))
    · rintro ⟨s,i⟩ U; exact dated _ _ (polarizei _ (ht i _) _)
    intro s k g h; refine ⟨Equiv.prodCongr (skyEquiv s) (Equiv.refl _),?_,?_⟩
    · rintro ⟨p,i⟩; change (Y.bud i).image (act (pod s p))=((Y.bud i).image (act p)).image (act s); rw [podA,image_image]; rfl
    rintro ⟨p,i⟩ U; change Diode N s k g (averageC c • spice p (Y.mean i (sky p (sky s U))))= averageC c • spice (pod s p) (Y.mean i (sky (pod s p) U)); rw [skying,eSM _ (phare _)]; apply congr_arg; change sways _ (sways _ _)=_; rw [leaps,← copies_mul,← beset _ _ _ _ g (ink p)]; exact coinT (Y.mean i _) (ht i _) (Strut.comb h (assured p)) (assured _)
lemma voyage (U:Grid c)(P:EvenA c N)(ht:∀ i: Strut c,HasSum (fun k=> spice i (Y.mean k (sky i U))) P): HasSum (fun i=> (HGrace Y).mean i U) P:=by
   suffices he : (∑ _i:Strut c,averageC c • P)=P from he ▸ (show HasSum (fun i: Strut c × ι=> (HGrace Y).mean i U) _ from Beam.lapis (fun i: Strut c × ι=> (HGrace Y).mean i U) (fun _=>averageC c • P) fun i=> (ht i).const_smul (averageC c))
   unfold averageC; rw [sum_const,← Nat.cast_smul_eq_nsmul ℝ,card_univ,smul_smul,mul_inv_cancel₀ (by positivity), one_smul]
end YM.QCD.Ruby
