import YM.QCD.Smoke.Gust

/-! # through large ratios with no inherited width cost. The non-small constants in the newborns will depend on L. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Smoke
open Lattice Wilson Finset Filter Function Metric Extra Iteration RG Placement Laurent Exterior Work.F08 Precision Bloch Matrix
open scoped Matrix BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {L n c f : Side}{I:Type*}{η σ A C r D D':ℝ}{G:Gauge}{k:ℕ}
def shootG (ψ:Columns L)(E:I→PairG G)(p:I×Site L×(Fin 2→CompassG)):=reasonG ψ (E p.1) p.2.1 p.2.2
lemma shucks (E:I→PairG G) {ψ: Columns L}(hA:0≤A)(h:0<η)(he:0≤σ)(ht:σ≤η/2)(hp:∀ v:Axis,(ψ (some v)).strip η (A/(L.val:ℝ)^3))(hg:Palisade E σ C) : Palisade (shootG ψ E) σ (cashRegister 2 η A / (L.val:ℝ)^2*C):=by
  let w:ℝ:= L.val; have hw:0<w:=side_pos L
  let u:= cashRegister 2 η (A/w^3)
  have hh (i:I)(x: Site L): Charged (fun j=> (reasonG ψ (E i) x j).atom) σ (u*(E i).atom.budget σ):= muster (E i) x he h ht (fun j=>by obtain ⟨a,hh⟩:=Option.isSome_iff_exists.mp (hg.1 i j); rw [hh]; exact hp a)
  have he' (i:I): 0 ≤ u*(E i).atom.budget σ:=Cost.nonneg (hh i 0)
  refine ⟨fun _ _=>rfl,fun _=> relocated_symm _ (hg.2.1 _) _ _ _,?_⟩
  have hx: cashRegister 2 η A/w^2=(Fintype.card (Site L):ℝ)*u:=by unfold u cashRegister; rw [site_card,Nat.cast_pow]; unfold w; field_simp
  rw [show cashRegister 2 η A/(L.val:ℝ)^2=_ from hx]; apply Cost.product (Cost.scale hg.2.2 _ (by unfold u cashRegister; have hx:= passage_pos h; positivity))
  intro i; rw [mul_assoc]; exact Cost.product (Cost.finite _ (he' i)) (hh i)
variable {g : Ratio c f} {ψ : Columns g.count} {F : Flux G f}{V:Flux G c}

def aggregateG (ψ:Columns L)(v: Pattern G k)(r:Site L)(U:Flux G c)(x:Site c)(b:Fin k→G.ColorIndex)(j:Fin k)(p:CompassG):ℝ:= worthG ψ v r p j * grad (zephyr p.2) (U p.1 (b j)) (x+wrap c (endingG r v p.2 j))
lemma aggregate_sum (ψ:Columns L)(v:Pattern G k)(r:Site L)(x:Site c)(V:Flux G c)(b:Fin k→G.ColorIndex)(i:Fin k)(ht:0<η)(h:(ψ (v.op i)).strip η A): Summable fun j=> |aggregateG ψ v r V x b i j|:= by
  have hx := cardsG v r i (ψ:=ψ) (show 0≤(0:ℝ) from le_rfl) ht (show 0≤η/2 from by linarith) h; simp only [zero_mul,Real.exp_zero,mul_one] at hx
  let B (u:Axis×PlaqAxes×Site c):= |grad u.1 (V u.2.1 (b i)) u.2.2|
  unfold aggregateG; simp_rw [abs_mul]; refine (hx.2.1.mul_right (∑ i,B i)).of_nonneg_of_le (fun _ =>by positivity) (fun j=> mul_le_mul_of_nonneg_left (single_le_sum (f:=B) (fun _ _=>abs_nonneg _) (mem_univ (_,_,_))) (abs_nonneg _))
lemma aggregate_roll (x:Site c) (v: Pattern G k)(b: Fin k→G.ColorIndex)(i:Fin k)(r:Site g.count)(hu : (v.op i).isSome)(he:Placement.Substitution g ψ F V)(h:Cancels ψ)(hk:0<η)(hv:(ψ (v.op i)).strip η A):
    ∑' p,aggregateG ψ v r V x b i p= Iteration.read (v.op i) (F (v.atom.leg i).plaq (b i)) (g.assemble (x,r)+ wrap f (v.atom.leg i).offset):=by
  have hs:= (aggregate_sum ψ v r x V b i hk hv).of_abs
  let s:= v.atom.leg i; let a:= x+ wrap c (carry r s.offset)
  rw [hs.tsum_prod,tsum_fintype,he,moves_parent,moves_residue,g.assemble_res,g.assemble_parent]
  apply sum_congr rfl; intro j _
  let W:=V j (b i); let M:= entry ψ v r (fun _=>j) i
  have hz : HasSum M 0:=by obtain ⟨d,hp⟩:= Option.isSome_iff_exists.mp hu; unfold M entry; simp_rw [hp]; exact h ..
  have hh p : ∑ l: Lift.Piece (taper p), aggregateG ψ v r V x b i (j,⟨p,l⟩)= M p*(W (a+wrap c p) - W a):=by
    have hu:= Lift.telescopes W a 0 (taper p); rw [show stop (0:Cover) (taper p)=p from route_end ..,map_zero,add_zero] at hu; rw [hu,mul_sum]
    apply sum_congr rfl; intro l _; unfold aggregateG endingG worthG; rw [map_add,← add_assoc, mul_assoc]
    rfl
  have h' := hs.prod_factor j
  rw [h'.tsum_sigma]; change (∑' p:Cover, ∑' l:Lift.Piece (taper p), _)=∑' y:Cover,M y*W (a+wrap c y); simp_rw [tsum_fintype,hh]
  have hRR:=h'.sigma; simp_rw [tsum_fintype,hh] at hRR
  have hT:= hRR.hasSum.add (hz.mul_right (W a)); simp only [zero_mul,add_zero] at hT; exact (HasSum.congr_fun hT (fun _=>by ring)).tsum_eq.symm -- inspect

lemma sum_up (v: PairG G)(r:Site g.count)(x:Site c)(ht:both v)(h: Placement.Substitution g ψ F V)(hc:Cancels ψ)(hp:0<η)(he:0≤σ)(hh:σ≤η/2)(hs:∀ i,(ψ (v.op i)).strip η A): ∑' p, (reasonG ψ v r p).sample V x=v.sample F (g.assemble (x,r)):=by
  let H:=aggregateG ψ v r V x; have hw b:= Cost.tsum_pi (f:=H b) (fun i=> aggregate_sum ψ v r x V b i hp (hs i)); have hy (p:Fin 2→CompassG):(reasonG ψ v r p).sample V x=∑ b,v.atom.coeff b* ∏ j,H b j (p j):=by
    unfold Pattern.sample; simp only [reasonG,relocate,slot_plaq,slot_offset,Iteration.read,Option.elim,H,aggregateG,prod_mul_distrib]; apply sum_congr rfl; intros; ring
  simp_rw [hy]; simp_rw [Summable.tsum_finsetSum (fun b _=> (hw b).1.of_abs.mul_left _),tsum_mul_left,(hw _).2]; apply sum_congr rfl; intro i _
  congr 1; exact prod_congr rfl (fun j _=>aggregate_roll x _ _ j _ (ht j) h hc hp (hs j))
lemma shoot_real {E:I→PairG G} (hA:0≤A)(h:0<η)(he:0≤σ)(ht:σ≤η/2)(hp:∀ v:Axis,(ψ (some v)).strip η (A/(g.count.val:ℝ)^3))(hg:Palisade E σ C)(hh: Placement.Substitution g ψ F V)(hx:Cancels ψ) : total (shootG ψ E) V=total E F :=by
  have hv:= net_summable (shootG ψ E) V he (shucks E hA h he ht hp hg).2.2; unfold total; rw [hv.tsum_prod]; apply tsum_congr; intro i
  rw [(hv.prod_factor i).tsum_prod,tsum_fintype, ← Equiv.sum_comp g.splitSites.symm (fun z=> (E i).sample F z),Fintype.sum_prod_type,sum_comm (f:=fun x r=> (E i).sample F _)] -- check
  apply sum_congr rfl; intro r _; change (∑' p, ∑ x, (reasonG ψ (E i) r p).sample V x) = _
  have H j : (ψ ((E i).op j)).strip η (A/(g.count.val:ℝ)^3):=by obtain ⟨d,h⟩:=Option.isSome_iff_exists.mp (hg.1 i j); rw [h]; exact hp d
  rw [Summable.tsum_finsetSum (fun x _=>sample_summable (reasonG ψ (E i) r) V he (muster _ _ he h ht H) x)]
  exact sum_congr rfl fun x _=> sum_up _ r x (hg.1 i) hh hx h he ht H
end YM.QCD.Smoke
