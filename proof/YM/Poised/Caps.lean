import YM.Poised.Amber
/-! # Grade blocks from actual polynomial reader. post-threshold unwinding is mono, uniform pre.As requested independent coefficient units. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type}{d k n:ℕ}{c l:Side}
namespace Facets
open Pipes QCD.Kit QCD.Flume QCD.Cove QCD.Creek QCD.Loom QCD.Flume QCD.Fork QCD.Port QCD.Brick Lining Lining.Ferry
open Precision Pressure Garden Run Laurent Carrier Next.Free QCD.Kit
open PhysicalNext.JointLoad Palette Steed Beacon MultiNext.SignedSource
open Counting Counting.Click Display Costs Sieve Chute PhysicalNext.Repeat PhysicalNext.Repeat.Brim MassiveQCD.Plate Lining.Temper Collage Carte.Hem Papyrus Stative
variable {R:BudgetPoint}{V:Support c}{o:Site c}{F:Grid c→Lat.Fields c 6}{a t:ℝ}{r K:ℕ}
structure Saturated (x:Pol d)(w l e:ℕ): Prop where
    kept p:coord p x≠0→ weight p=w ∧ life p.1=l ∧ p.2.card=e
namespace Saturated
variable {x:Label d}{w i e:ℕ}(h:Saturated x.val w i e)
include h
lemma at_zeroS(k:ℕ)(hp:w≠k): geometry k x.val=0:=by
    apply (zBasis d).repr.injective; ext m; change coord m (geometry k x.val)= coord m 0; rw [map_zero,geo_basis]; split; next he=> exact not_ne_iff.mp fun hc=> hp ((h.kept m hc).1 ▸ he)
    next _=>rfl
lemma engraved (H:TaperHol)(b:Cover)(F:Grid c→ Lat.Fields c 6)(he: Beacon.ActionTest H b F x.val) (q:ℕ)(hQ:q≤w)(hh:q≤d+1) : ∀ (J:Labels.Jet su)(t:ℕ), t<q → leading t (Beacon.moment (d:=d) H b J F) =0:=by
   intro J t ht; apply leading_zero_iff.mpr; rw [(he J).2.2 t (by omega), ← funext (observe _ _), order_test,at_zeroS h t (by omega), map_zero,smul_zero]
lemma at_rank (t v:ℝ) : dimming t v d x=((t:ℂ)^i*(v:ℂ)^e) • x:=by
    apply Subtype.ext; apply (zBasis d).repr.injective; ext m; change coord m (Sieve.widths t v x.val)= coord m _; rw [rank_fee,Submodule.coe_smul_of_tower,map_smul]
    by_cases he:coord m x.val=0; · rw [he,mul_zero,smul_zero]
    rw [(h.kept _ he).2.1,(h.kept _ he).2.2]; rfl
lemma innate (B:Basis (Fog d) ℂ (Label d)) (t v:ℝ): watch B x t v= |t|^i*|v|^e*‖cose B x‖:=by rw [watch,at_rank h,cose,map_smul,norm_smul,norm_mul,norm_pow,norm_pow,Complex.norm_real, Complex.norm_real]; rfl
end Saturated
lemma fare_pay (i:PowerPair d)(x:Pol d)(t v:ℝ) : ‖fare i x t v‖=|t|^life i.1*|v|^i.2.card*‖coord i x‖:=by rw [Stative.fare,rank_fee,norm_mul,norm_mul,norm_pow,norm_pow,Complex.norm_real,Complex.norm_real];rfl
variable {τ σ φ v ps :ℝ}{p:Powers}{e i:ℕ}
def changeB (R:BudgetPoint) (t:ℝ)(h:0<t)(hp:t ≤1):BudgetPoint:={R with threshold:=t,threshold_pos:=h,threshold_le:=hp}
def worth (p n:ℕ):ℝ := ((1+(p:ℝ))^n)⁻¹
lemma worth_ge (p n:ℕ) :0<worth p n ∧ worth p n ≤1:= by unfold worth; exact ⟨by positivity,inv_le_one_of_one_le₀ (one_le_pow₀ (by simp))⟩
lemma sizedT (R:BudgetPoint)(p:ℕ)(b:Cover)(t:ℝ)(h:0<t)(hp:t≤1)(hH:t≤ worth p R.power)(i:Edge (Site l))(hi:Mom.needed (pot p l b) i): Lyre.width (changeB R t h hp) (wrap l b) i ≤1:=by
    change t * (1+ (separation i.1 (wrap l b):ℝ))^R.power ≤ 1; let A:ℝ:= (1+(p:ℝ))^ R.power; have ha:1 ≤ A:=one_le_pow₀ (by simp)
    refine (mul_le_mul (hH : t ≤ A⁻¹) (pow_le_pow_left₀ (by positivity) (add_le_add_right (Nat.cast_le.mpr (placed_s _ _ _ hi.1)) _) _) (by positivity) (by change 0≤ A⁻¹; positivity)).trans_eq (inv_mul_cancel₀ (by linarith))
private lemma cold {A B p:ℝ}{i j:ℕ}(hP:0<p)(hm:∀ x:ℝ,0<x→x≤p→ x^i*A ≤ x^j*B)(hj:i<j): A≤0:=by
   let k:=j-i; have hk:k≠0:=by unfold k; omega
   have h(x:ℝ)(hx:0<x)(hr:x≤p) : A≤ x^k*B:= by apply le_of_mul_le_mul_left _ (pow_pos hx i); rw [← mul_assoc, ← pow_add,show i+k=j by unfold k; omega]; exact hm x hx hr
   have hv : Tendsto (fun x:ℝ=> x^k * B) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (𝓝 0):=by
      simpa only [ContinuousWithinAt,zero_pow hk, zero_mul] using! (show Continuous (fun x:ℝ=>x^k*B) from by fun_prop).continuousWithinAt (x:=0) (s:=Set.Ioi 0)
   apply le_of_tendsto_of_tendsto tendsto_const_nhds hv _ -- eventually use
   filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hP)] with x hx hy using h x hx (show x<p from hy).le
private lemma thaw {A B:ℝ}{i j:ℕ}(hm:∀ x:ℝ,0<x→ x^i*A ≤ x^j*B)(hj:j < i) : A ≤0:= by
   apply cold (B:=B) (p:=1) (i:=j) (j:=i) zero_lt_one _ hj; intro x hx hp; have he:=hm x⁻¹ (inv_pos.mpr hx); rw [inv_pow,inv_pow, inv_mul_le_iff₀ (pow_pos hx i),mul_left_comm] at he; exact (le_inv_mul_iff₀ (pow_pos hx j)).mp he -- fix
variable (U: Source.Hol su)(A:Exhibit U)(F₀: Basis (Fog d) ℂ (Label d))
-- Uniform post-step. X fixed strict pot, H arbitrary. No arbitrary continuum extension read, Call.He.
lemma graded (i j k p m n z D' w l e:ℕ) (V:Hera.Rights su n)(H:TaperHol)(u:Rings d)(hp: Permit.used_bound (A.t d) p)(hσ:0 < σ)(hτ:0 ≤ τ)(hz:Fintype.card (ZBand d) < z)(hD:d < n)(hn:n ≤ m)(hk:4 ≤ k): ∃ C:ℝ,0  ≤  C ∧ ∀ (P:Flight j k)(K:KernelChoices)(c l':Side)(h:l'.val=c.val*P.L.val)(T: Tube su (Flight.visit P K h))(R:BudgetPoint)(v u':ℕ)(b b':Cover)(Y:Support c), Cruising (sliceL P h) (pot (p+1) l' b) Y b b' u' v → R.power=i → R.order=m→ 2*(p+1)< l'.val→T.R.A0.strip σ τ→(∀ (u v:Pipes.Shell)(x:Cover), Width σ τ (arch P u v x)) → ∀ (x:Label d)(y:Pol d), Saturated x.val w l e → y∈ UV.cap d → Beacon.ActionTest H b' (kite P h T (Realize.placed (A.t d) l' b (A.lead d x)) Y) y →
      (coord u.val y≠0→ l  ≤  life u.val.1 ∧ e=u.val.2.card) ∧ ‖coord u.val y‖  ≤  C * ratioP d (n+1) v * ‖cose F₀ x‖:=by
    obtain ⟨B,hB,H₀⟩:= massy U A F₀ hp i m D' z
    obtain ⟨C,hC,H'⟩:= pastL u H j k D' V σ τ 1 zero_le_one hσ hτ hD
    let T:=worth (p+1) i; have hY:0 < T:=(worth_ge ..).1
    let D:=C*B; have hD':0 ≤ D:=mul_nonneg hC hB
    let q:=life u.val.1; let V':= D*T^l; let W:= (T^q)⁻¹*V'
    refine ⟨W,by unfold W V'; positivity,?_⟩; intro P K c l' h T₀ R v u' b b' Y hV ha he hx0 hT hZ x y h0 hx hX
    let F:= Realize.placed (A.t d) l' b (A.lead d x); let A:=‖coord u.val y‖; let N:=‖cose F₀ x‖; let N':=ratioP d (n+1) v; let E:=u.val.2.card
    have ht (t v':ℝ)(ht:0<t)(hv:0 < v')(hh:t  ≤  T) : t^q*v'^E*A  ≤  D*N'*(t^l*v'^e*N):=by
        have hs : t ≤ 1:=hh.trans (worth_ge _ _).2; let R':=changeB R t ht hs; have hP:Harbor (pot (p+1) l' b) Y b b' T₀ R' σ τ 1 v' v' t u' v :=⟨hV,hT,fun i j k=> hZ j k i,hv.le,hv,by simp,ht.le, show t  ≤  2*t by linarith,hs,fun i hi=>sizedT R (p+1) _ t ht hs (ha.symm ▸ hh) i hi,hk⟩
        have he := (H' P K c l' h T₀ R' v u' _ _ _ _ _ _ _ _ z (he.symm ▸ hn) hz hP _ _ (H₀ b R' l' (by exact ha) (by exact he) hx0 v' hv x) hx hX).1
        rw [fare_pay, abs_of_pos ht,abs_of_pos hv,h0.innate F₀ R'.threshold v', show R'.threshold=t from rfl,abs_of_pos ht,abs_of_pos hv] at he
        exact he.trans_eq (by unfold D N N'; ring)
    have hxV : ∀ v':ℝ,0<v'→ v'^E*(T^q*A)  ≤  v'^e*(D*N'*T^l*N) :=by intro v' hv; apply (le_trans (le_of_eq _) ((ht T v' hY hv le_rfl).trans_eq _)) <;> ring
    constructor
    · intro hν; have he :0<A:= norm_pos_iff.mpr hν; have hz' :0<T^q*A:= by positivity
      constructor
      · by_contra hp; have hz:q < l:=lt_of_not_ge hp
        have hv:= cold (i:=q) (j:=l) (A:=A) (B:=D*N'*N) hY (by
            intro t ht' hT; apply le_trans _ ((ht t 1 ht' zero_lt_one hT).trans_eq _)
            · simp
            ring) hz; linarith
      by_contra hP; rcases lt_or_gt_of_ne (show e ≠ E from hP) with h|h
      · exact hz'.not_ge (thaw hxV h)
      exact hz'.not_ge (cold (p:=1) zero_lt_one (fun x hx _=>hxV x hx) h)
    specialize ht T 1 hY zero_lt_one le_rfl; rw [one_pow,one_pow,mul_one,mul_one] at ht; change A  ≤  ((T^q)⁻¹*V'*N')*N; have he':0<T^q:=by positivity
    rw [mul_assoc ((T^q)⁻¹),mul_assoc ((T^q)⁻¹)]; exact (le_inv_mul_iff₀ he').mpr (ht.trans_eq (by unfold V'; ring))

end Facets
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Facets.graded
