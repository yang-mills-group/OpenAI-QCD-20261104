import YM.Bank.Knot
/-! Exact prices true unmarked, retaining coarse p factor -/
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Merchant
open Wilson Lattice RG Precision Laurent Bloch Function Finset Exterior AnalyticBridge.LocalGaussianLaws.Current
open Matrix Filter Metric Work.F06 Next.Free Learn Knot
open scoped Matrix BigOperators Topology ComplexConjugate InnerProductSpace Matrix.Norms.L2Operator
variable {c f L: Side}{k j:ℕ} {a b r:ℝ} {p: Momentum}
section basic
lemma chip_bill (hp:p∈cube zone)(i:Axis) : ‖chip (p i)‖ ≤ meter.high*‖p‖ := (meter.above _ (zone_in_disk p hp i)).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm _ _) meter.high_pos.le)
def relay (n:ℕ) : ℝ:= ∑ i:Axis,meter.high*‖left ℂ n i‖
lemma relay_pos (i:ℕ):0 ≤ relay i:=sum_nonneg fun _ _=>mul_nonneg meter.high_pos.le (norm_nonneg _)
lemma lay_cost (hp:p∈cube zone) (n:ℕ): ‖signal 1 n p‖ ≤ relay n*‖p‖:=by
     unfold signal wedge relay; rw [sum_mul]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro i _;
     rw [norm_smul,tripQ,show ((1:Side).val:ℂ)=1 from by norm_num,one_mul,mul_right_comm]; exact mul_le_mul_of_nonneg_right (chip_bill hp _) (norm_nonneg _)
def mapping (I V:Type)[Fintype I][DecidableEq I][Fintype V][DecidableEq V] : (I→V→ℂ) →L[ℂ] Matrix I V ℂ := (Matrix.ofLinearEquiv ℂ).toLinearMap.toContinuousLinearMap -- name
lemma on_base (hp:p∈baseCube) : p∈ cube zone:= mem_cube_real (base_subset_realCube zone_pos hp) zone_pos
def ℳ:=mapping (TypeFace 2) (TypeFace 2)
def bankT (b:ℝ):= relay 1*‖ℳ‖*b*relay 1
lemma bankT_pos (b:ℝ)(h:0≤b):0≤ bankT b:= mul_nonneg (mul_nonneg (mul_nonneg (relay_pos _) (norm_nonneg ℳ)) h) (relay_pos _)
lemma base_cost (hp:p∈baseCube){B:Bed} (hb:0≤b) (hr:B.metric.strip r b) (he:0≤r) : ‖live B.metric p‖ ≤ bankT b*‖p‖^2:=by
     let D:=signal 1 1 p; let X:= B.metric.read p; let U:=relay 1; have hw:‖D‖ ≤ U*‖p‖:= lay_cost (on_base hp) _
     have hx:‖X‖ ≤‖ℳ‖*b:=by
         apply (ℳ.le_opNorm (of.symm X)).trans
         apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); exact (pi_norm_le_iff_of_nonneg hb).mpr fun i => (pi_norm_le_iff_of_nonneg hb).mpr fun j => row_entry_le hr he p hp.1 _ _
     have ht := norm_nonneg D|>.trans hw
     rw [live_gram hp]; exact (l2_opNorm_mul (Dᴴ*X) D).trans ((mul_le_mul ((l2_opNorm_mul Dᴴ X).trans (mul_le_mul ((l2_opNorm_conjTranspose D).trans_le hw) hx (norm_nonneg _) ht)) hw (norm_nonneg _) (mul_nonneg ht (mul_nonneg (norm_nonneg ℳ) hb))).trans_eq (by unfold bankT U; ring))
lemma core (l:Site L)(hp:p∈baseCube) : ‖p‖ ≤4*(L.val:ℝ)*‖aliasAt p l‖ := by
   let s:=aliasAt p l; have hL:= side_pos L; by_cases he:l=0
   · subst l; rw [alias_zero_eq,narrow,norm_smul,norm_inv,Complex.norm_natCast]; have hp : (L.val:ℝ)*(L.val:ℝ)⁻¹=1:=mul_inv_cancel₀ hL.ne'; nlinarith only [hp,norm_nonneg p]
   obtain ⟨i,hi⟩:=hit_grade l; have he' : lift l i≠0:=by intro h; have hd:=grade_gt he; rw [hi] at hd; simp [up,h] at hd
   have hp' := scaled_alias_lower _ (on_base hp) _ he'
   have hk: Real.pi/4 ≤ (L.val:ℝ)*‖s‖:= (le_mul_of_one_le_right (by positivity) (up_ge _ _)).trans (hp'.trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm s i) hL.le)); exact (QCD.Pearl.cap_base hp).trans (by linarith)
lemma pace (hp:p∈cube zone) (l:Site L) : ‖aliasAt p l‖ ≤ 2*Real.pi/(L.val:ℝ)*grade l:=by
   have ht:=grade_pos l; have hu:= side_pos L; apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro i;
   rw [div_mul_eq_mul_div,le_div_iff₀ hu,mul_comm]; exact (scaled_alias_upper _ hp i).trans (mul_le_mul_of_nonneg_left (up_le _ _) (by positivity))
def μ : ℝ:= meter.high*(2*Real.pi)
lemma μpos : 0<μ:= mul_pos meter.high_pos (by positivity)
lemma stiletto (hp:p∈baseCube)(u:List Axis): ‖listChip p u‖ ≤ (meter.high*‖p‖)^u.length :=by
   induction u with
   | nil=>simp [listChip]
   | cons a s ih=> simp only [listChip,List.map_cons,List.prod_cons,norm_mul,List.length_cons]; rw [pow_succ']; exact mul_le_mul (chip_bill (on_base hp) _) ih (norm_nonneg _) (mul_nonneg meter.high_pos.le (norm_nonneg _))
lemma distance (hp:p∈baseCube)(l:Site L)(ho:Odd L.val)(u:List Axis) : ‖listChip (aliasAt p l) u‖ ≤ grade l ^ u.length*(μ^(u.length)/(L.val:ℝ)^u.length):=by
   apply (stiletto (alias_base hp l ho) _).trans; rw [← div_pow,← mul_pow]; apply pow_le_pow_left₀ (mul_nonneg meter.high_pos.le (norm_nonneg _)); exact (mul_le_mul_of_nonneg_left (pace (on_base hp) l) meter.high_pos.le).trans_eq (by unfold μ; ring)
lemma fora (j:ℕ) : ∃ B:ℝ,0≤B∧∀ (L:Side)(l:Site L)(p:Momentum), Odd L.val→ p∈baseCube→ ‖sprout j L (aliasAt p l)‖ ≤ B*decay j l∧ ‖mask 1 (spindle j L (aliasAt p l))‖≤B*decay j l:=by
   obtain ⟨b,hb,H⟩:= alias_rail
   let C:=max 1 b; have hC : 0<C:= one_pos.trans_le (le_max_left ..); let B:=(b^4)^j; have hB:0<B:=pow_pos (pow_pos hb _) _
   refine ⟨B*C,by positivity,fun L l p ho hp=>?_⟩
   let u := aliasAt p l; have he := H L ho p (on_base hp) l; have hi : ‖area L u‖ ≤ b^4*(mix l)⁻¹ := by
      unfold area; rw [norm_prod]; apply (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i (_:i∈Finset.univ)=> (he i).2)).trans; simp [Finset.prod_mul_distrib,Axis,mix]
   have hx : ‖sprout j L u‖≤B*decay j l:=by unfold sprout; rw [norm_pow]; apply (pow_le_pow_left₀ (norm_nonneg _) hi j).trans; unfold B decay; rw [mul_pow, inv_pow]
   refine ⟨hx.trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hB.le (le_max_left ..)) (decay_pos _ _).le),?_⟩
   let f(i:TypeFace 1):= spindle j L u (axisEquiv.symm i); rw [show mask 1 _= diagonal f from Matrix.ext fun i y=>mask_value _ i y, l2_opNorm_diagonal]
   have hd:=decay_pos l j
   apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro i; unfold f spindle; rw [norm_mul,mul_right_comm]; have hm:= he (axisEquiv.symm i); exact mul_le_mul hx (hm.1.trans ((mul_le_of_le_one_right hb.le (inv_le_one_of_one_le₀ (up_ge ..))).trans (le_max_right ..))) (norm_nonneg _) (by positivity)
end basic
-- sum of priced occurrences. Keep coarse norm p to finance low covariance.G.
lemma currency (a b:ℝ)(ha:0<a)(hb:0≤b) (j:ℕ) : ∃ C:ℝ,0≤C ∧∀ {c f:Side}(g:Ratio c f)(F B:Bed)(b':ℝ), Odd g.count.val → F.metric.safe → (∃ r:ℝ,0≤r ∧ B.metric.strip r b) → Numeric (F.metric.acts f) a b' →
     ∀ (p:Site c)(l:Site g.count),‖crow j g B F (mon p) l‖ ≤ C*decay j l*‖mon p‖/(g.count.val:ℝ)^2:=by
   obtain ⟨u,hu,H⟩:= fora j; let C:=relay 1*u*bankT b*(lum a)⁻¹; have hv:=bankT_pos b hb; have hw:=luminous ha; have hd:=relay_pos 1
   refine ⟨C*4,by unfold C; positivity,fun {c f} g F B b' ho hF ⟨r,hr,h⟩ hh p l=>?_⟩
   let L := g.count; let P:=mon p; let i:=QCD.Flume.twins g p l; let v:= aliasAt P l; have hx: mon i=v:= twin_mon g ho ..
   let x:=(L.val:ℝ); let y:= decay j l; have hz:=decay_pos l j; have hs : 0<x:=side_pos _
   have he := core l (mon_mem c p); change ‖P‖≤4*x*‖v‖ at he
   let w:= live B.metric P
   have hl :‖w‖ ≤ bankT b *‖P‖^2:=base_cost (mon_mem _ p) hb h hr
   by_cases hf:v=0
   · unfold crow; dsimp only; change ‖starΔ F v*_ * w‖ ≤ _; rw [starΔ,hf,outside,Matrix.zero_mul,Matrix.zero_mul,Matrix.zero_mul,norm_zero]; have hu:0≤C:=by unfold C; positivity
     positivity
   have ht:=purse _ hh ha i hF (hx.symm ▸ hf)
   have hk:=alias_base (mon_mem c p) l ho; let t:= ‖v‖; have ht':0<t:=norm_pos_iff.mpr hf
   have hy:‖starΔ F v‖ ≤ relay 1*t*(lum a*t^2)⁻¹:= (l2_opNorm_mul ..).trans (mul_le_mul (lay_cost (on_base hk) _) (by rw [hx] at ht; exact ht.2) (norm_nonneg _) (mul_nonneg hd ht'.le))
   let Y:= (stageVolume L)⁻¹ • (((L.val:ℂ) • mask 1 (spindle j L v))ᴴ)
   have hj : ‖Y‖ ≤ x⁻¹^4 *(x*(u*y)):=by unfold Y; rw [norm_smul, l2_opNorm_conjTranspose, norm_smul, Complex.norm_natCast, norm_inv,stageVolume,norm_pow,Complex.norm_natCast, inv_pow]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (H L l _ ho (mon_mem c p)).2 hs.le) (by positivity)
   change ‖starΔ F v* Y*w‖ ≤ C*4*y*‖P‖/x^2
   apply (l2_opNorm_mul ..).trans; apply (mul_le_mul ((l2_opNorm_mul ..).trans (mul_le_mul hy hj (norm_nonneg _) ((norm_nonneg _).trans hy))) hl (norm_nonneg _) (by unfold y; change 0<t at ht'; positivity)).trans
   let z:=‖P‖; have hZ:0≤z:=norm_nonneg _; have ht:C*y/x^3/t*z ≥ 0:=by unfold C y; positivity
   calc
     _ = C*y/x^3/t*z*z:=by unfold C z; field_simp
     _ ≤ C*y/x^3/t*z*(4*x*t):=mul_le_mul_of_nonneg_left he ht
     _ = _:=by unfold z; field_simp
end YM.Bank.Merchant
#print axioms YM.Bank.Merchant.currency
