import YM.Patria.Brute
import YM.Massive.Lining.Cameo
/-! Full tapered frames rotation. No symmetry at tiny lattices required. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Canvas
open Filter Function Set MeasureTheory Lattice Labels Source RG Wilson Source.Drops
open scoped Matrix.Norms.Frobenius BigOperators Topology
open QCD SourceRead
variable {G : Gauge}
-- share conventions
theorem motion_site (s : Signed) (x : Cover) :
    Ortho.motion s.ortho (vector x) = vector (s.act x) := by
  rw [Ortho.motion_at, Signed.ortho_move]
  apply PiLp.ext
  intro k
  obtain ⟨i, rfl⟩ := s.perm.surjective k
  cases h : s.flip i <;> simp [vector, h]

private theorem motion_axis (s : Signed) (i : Axis) :
    Ortho.motion s.ortho (basis i) = (if s.flip i then (-1 : ℝ) else 1) • basis (s.perm i) := by
  apply PiLp.ext
  intro k
  rw [Ortho.motion_at, Ortho.move, M4.move_basis]
  by_cases h : s.perm i = k
  · subst k
    cases hf : s.flip i <;> simp [Signed.ortho, Signed.matrix_at, hf]
  · cases hf : s.flip i <;> simp [Signed.ortho, Signed.matrix_at, h, Ne.symm h]

private theorem vector_prev (x : Cover) (i : Axis) :
    vector (x - step i) = vector x - basis i := by
  apply PiLp.ext
  intro k
  by_cases hk : k = i <;> simp [vector, hk]

private theorem potential_turn (s : Signed) (d : ℕ) (J : Jet G) (i : Axis) (z : E4) :
    potential d (changedJet (fun _ => Taylor.turn s.ortho⁻¹) J) i z =
      (if s.flip i then (-1 : ℝ) else 1) • potential d J (s.perm i) (Ortho.motion s.ortho z) := by
  unfold potential
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [changedJet, Taylor.turn_value, inv_inv, Ortho.motion_at]
  rw [Finset.sum_eq_single_of_mem (s.perm i) (Finset.mem_univ _)]
  · rw [show s.ortho⁻¹.val i (s.perm i) = star (s.matrix (s.perm i) i) from rfl]
    simp only [star_trivial, s.matrix_at, ↓reduceIte]
  · intro k _ hk
    rw [show s.ortho⁻¹.val i k = star (s.matrix k i) from rfl]
    simp [Signed.matrix_at, Ne.symm hk]

private theorem part_turn (s : Signed) (d : ℕ) (J : Jet G) (h t : ℝ) (x : Cover) (i : Axis) :
    partConnection d (changedJet (fun _ => Taylor.turn s.ortho⁻¹) J) h (x, i) t =
      h • ((if s.flip i then (-1 : ℝ) else 1) •
        potential d J (s.perm i)
          (h • (vector (s.act x) + t • ((if s.flip i then (-1 : ℝ) else 1) • basis (s.perm i))))) := by
  change h • potential d _ i (h • (vector x + t • basis i)) = _
  rw [potential_turn, map_smul, map_add, map_smul, motion_axis, motion_site]

variable (s:Signed)(H:TaperHol) {c:Side}(d:ℕ)(J:Jet su)(v:ℝ)(x:Cover)(i:Axis)(t:ℝ)
abbrev JQ := changedJet (fun _=>Labels.Taylor.turn s.ortho⁻¹) J
lemma glaze(c:Side) : let σ:ℝ:=if s.flip i then -1 else 1; H.T.χ ((c.val:ℝ)⁻¹ • (vector x+t • basis i))= H.T.χ ((c.val:ℝ)⁻¹ • (vector (s.act x)+t • (σ • basis (s.perm i)))):=by intro σ; rw [← motion_axis,← motion_site,← map_smul,← map_add,← map_smul,Ortho.motion_at,H.T.even]
lemma swirls (r:Side): ((posDir i).rotate s).read (fun l:Edge Cover=> H.flow r d J v l 1) (s.act x)= H.flow r d (JQ s J) v (x,i) 1:=by
   have hp:= H.solves r d (JQ s J) v (x,i)
   cases hg:s.flip i
   · have he : H.T.connection r d (JQ s J) v (x,i)= H.T.connection r d J v (s.act x,s.perm i):=by
         funext u; unfold Taper.connection; dsimp only; rw [glaze s H]; unfold JQ; rw [part_turn]; simp [partConnection,vector,hg] -- remove
     rw [he] at hp; rw [show (posDir i).rotate s=posDir (s.perm i) from (by simp [Step.rotate,posDir,hg]), Step.pos_read]; exact congr_fun ((H.solves ..).unique hp) 1
   let a:= s.perm i; let y :Edge Cover:= (s.act x - step a, a)
   have he : H.T.connection r d (JQ s J) v (x,i) = fun t=> - H.T.connection r d J v y (1-t):=by
       funext u; unfold Taper.connection y; dsimp only; rw [glaze s H x i u]; unfold JQ; rw [part_turn]
       let z:= vector (s.act x)- basis a+(1-u) • basis a; have hz : vector (s.act x)- basis a+(1-u) • basis a= vector (s.act x)+ -(u • basis a):=by rw [sub_smul,one_smul]; abel
       change _= -(_ • ((v^2) • Source.potential _ _ a ((v^2) • (vector (s.act x - step a)+(1-u) • basis a))))
       rw [vector_prev,hz]; simp only [a,hg,↓reduceIte, neg_one_smul, smul_neg] -- syntax
   rw [he] at hp; rw [show (posDir i).rotate s=negDir a from (by simp [a,Step.rotate,posDir,hg,negDir]), Step.neg_read]; let V:=H.flow r d J v y
   simpa only [sub_self, (H.solves r d J v y).1, mul_one] using congr_fun ((Work.G01.solves_backward (H.solves r d J v y)).unique hp) 1
lemma boundary (p:Cover)(x:Site c)(hp:wrap c p=x)(hv:∀ i, 2*(p i).natAbs ≤ c.val+2)(hh:Lattice.lift x ≠ p) : ∃ i, c.val ≤ 2*(p i).natAbs ∧ c.val≤2*(lift x i).natAbs+2:=by
    obtain ⟨i,hi⟩:= not_forall.mp (show ¬∀ i:Axis,- (c.val:ℤ)<2*p i∧2*p i ≤ (c.val:ℤ) from fun h=> hh (lift_eq_iff.mpr ⟨hp.symm,h⟩)); specialize hv i; let k:= lift x i
    obtain ⟨h1,h2⟩:= lift_centers x i; have hj : lift x i ≠ p i :=by omega
    have he:= Int.natAbs_le_of_dvd_ne_zero ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (show (↑(Lattice.lift x i):ZMod c.val)=(p i:ZMod c.val) from congr_fun ((wrap_lift x).trans hp.symm) i)) (sub_ne_zero.mpr (Ne.symm hj)); rw [Int.natAbs_natCast] at he; exact ⟨i,by omega,by omega⟩
variable (hc: 18 ≤ c.val)
include hc
lemma darkness (x:Cover)(i j:Axis)(hi:c.val ≤2*(x i).natAbs+2)(t:ℝ)(ht:t∈Ioo (-1:ℝ) 2) : H.T.χ ((c.val:ℝ)⁻¹ • (vector x+t • basis j))=0:=by
    have hh : (18:ℝ)≤ c.val:= by exact_mod_cast hc
    have hx: (c.val:ℝ) ≤ 2*|(x i:ℝ)|+2:=by rw [← Int.cast_abs,← Int.natCast_natAbs]; exact_mod_cast hi
    have hu: (c.val:ℝ)/4 ≤ |(x i:ℝ)+ t*basis j i|:=by
       have htV:|basis j i| ≤1:=by by_cases h:i=j <;> simp [h,Ne.symm]
       have hs: |t*basis j i| ≤2:= by rw [abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg _) htV).trans (abs_le.mpr ⟨by linarith [ht.1],ht.2.le⟩)
       have ht:= abs_add_le ((x i:ℝ)+ t*basis j i) (- (t*basis j i)); rw [abs_neg,add_neg_cancel_right] at ht; linarith
    apply H.T.outside i; change _≤|(c.val:ℝ)⁻¹ * ((x i:ℝ)+t* basis j i)|; rw [abs_mul,abs_inv,abs_of_nonneg (Nat.cast_nonneg _),mul_comm,← div_eq_mul_inv,le_div_iff₀ (by linarith)]; linarith
lemma dawn (x:Cover)(i j:Axis)(hi:c.val≤ 2*(x i).natAbs+2) : H.flow c d J v (x,j) 1=1:=by
    apply Source.Hol.agree (x:=1) (I:=Ioo (-1:ℝ) 2) (b:=0) isOpen_Ioo (convex_Ioo ..) (by simp) (A:=0) (v:=fun (_:ℝ)=> (1:su.El)) (fun t ht=>?_) (fun t _=>?_) (H.solves ..).1 (by norm_num) -- args names
    · have h:= (H.solves c d J v (x,j)).2 t; unfold Taper.connection at h; rw [darkness H hc _ _ j hi t ht, zero_smul] at h; exact h
    simp; exact hasDerivAt_const _ _
lemma corner(x:Cover)(j:Axis)(hp:∀ i, 2*(x i).natAbs ≤ c.val+2) : H.links c d J v (wrap c x,j) = H.flow c d J v (x,j) 1:=by
    unfold TaperHol.links; dsimp only; by_cases he: lift (wrap c x)=x; · rw [he]
    obtain ⟨i,h1,h2⟩:= boundary x (wrap c x) rfl hp he; rw [dawn H d J v hc _ _ j h2,dawn H d J v hc x i j (h1.trans (by omega))]
lemma reads : pull s 0 (H.links c d J v)=H.links c d (JQ s J) v:=by
   funext X; rcases X with ⟨x,i⟩; let y:= Lattice.lift x; let g:= s.perm i
   have h: ∀ j:Axis, 2*((s.act y) j).natAbs ≤ c.val:=by intro j; obtain ⟨j,rfl⟩:=s.perm.surjective j; have he:= lift_centers x j; unfold y; rw [Signed.act_at]; split <;> omega
   change ((posDir i).rotate s).read _ (affine s 0 x)= H.flow c d _ _ (y,i) 1; rw [affine,add_zero, ← swirls, show s.act x=wrap c (s.act y) from (by rw [←wrap_signed]; unfold y; simp)]
   cases hs : s.flip i
   · rw [show (posDir i).rotate s=posDir g by simp [Step.rotate,posDir,hs,g], Step.pos_read,Step.pos_read]; exact corner H d J v hc _ _ fun j=>le_trans (h j) (by omega)
   rw [show (posDir i).rotate s=negDir g by simp [Step.rotate,posDir,negDir,hs,g],Step.neg_read, Step.neg_read,show wrap c (s.act y)-Lattice.step g=wrap c (s.act y-step g) from (by simp)]
   apply congr_arg Inv.inv; apply corner; exact hc; intro j; have hh:= h j; simp only [Pi.sub_apply,step_apply]; split <;> omega
omit hc
lemma midnight (r:Side): conjugate ∘ (H.links r d J v)= H.links r d (changedJet (fun _=>UV.recolor) J) v:=by
   funext i; let J':= changedJet (fun _=>UV.recolor) J; let X: Edge Cover:=(lift i.1,i.2)
   have h: H.T.connection r d J' v X=fun u=>UV.reflectColor (H.T.connection r d J v X u):=by funext u; simp only [Taper.connection,J',partConnection,potential, changedJet,Papyrus.Scan.value_R,map_smul,map_sum]
   exact congr_fun ((Papyrus.Scan.conj_flow (H.solves r d J v X)).unique (h ▸ H.solves r d J' v X)) 1
end YM.Massive.Patria.Canvas
#print axioms YM.Massive.Patria.Canvas.reads
