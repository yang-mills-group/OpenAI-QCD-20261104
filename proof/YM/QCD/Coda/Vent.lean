import YM.QCD.Coda.Ice
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Coda
open Lattice Wilson Function Finset Filter Metric RG Precision Extra Iteration PhysicalNext.Repeat
open Lat Octave Kit Leaf Tee Port Garden Run Orbit Cove Loom Fleet
open ConnectedActivityE6 Blaze Brush Sienna NormedSpace Lantern Push MeasureTheory Tree Lat MeasureTheory
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
open Pressure Jets Reggae Tidings Grass Kites Flume Tee YM.Next.Free Oasis
variable {n f c:Side}{N j k B B':ℕ}
variable {S:Flight j k}{H:f.val=c.val*S.L.val}{w d v u t p C A b:ℝ}
local notation "G"=>sliceL S H
variable {X:Grid f→Sheet f} {W:ℕ→ Atom su 2}
lemma story (he:Species S H v u t p b B X)(V:Grid f)(F:ℕ):
   Kit.sheath 1 (ater S H V) (gauss (starPerf S H X F V))=(X V).det^F • gauss (Lat.copies F (foam S H X V)):=by
   let Q:=ater S H V (F:=F); let T:= starPerf S H X F V; let Y := Lat.copies F (X V);
   have h : joinD 1 Q T=Matrix.fromBlocks Y (-Qᴴ) (-Q) 1:=by simp only [joinD,Complex.ofReal_one,neg_smul,one_smul]; rw [show T+Qᴴ*Q=Y from (sprig F V X).symm]
   have hh:IsUnit Y.det:=by rw [show Y.det= _ from copies_det ..]; exact (he.sole _).pow _
   change Kit.sheath 1 Q (gauss T)= _; rw [← mul_one (gauss T), clothe,h,map_one,mul_one,marginal_schur _ _ _ _ hh, Matrix.neg_mul,Matrix.neg_mul,Matrix.mul_neg,neg_neg, ← show Lat.copies F (foam S H X V)= _ from (spool V F he).symm, show Y.det= (X V).det^F from copies_det ..]; simp
lemma streak (he:Species S H v u t p b B X)(V:Grid f)(N:ℕ)(W:ℕ→Atom su 2):
   (↑(Real.exp (-Extra.Iteration.action W V)):ℂ)^N • Kit.sheath 1 (ater S H V) (gauss (starPerf S H X N V))=(X 1).det^N • light _ (exp (mica (O:=S) H X W N V)):=by
   rw [story he V N]; let D:= Real.log (X V).det.re-Real.log (X 1).det.re; let B:=Extra.Iteration.action W V
   rw [Octave.mica, exp_add, map_mul _ (exp _)]; have hx : Reggae.baker c N (N*(D-B))= sparkF c N ((N:ℂ)*((D-B:ℝ):ℂ)):=by rw [gets,← Complex.ofReal_natCast,← Complex.ofReal_mul]; rfl
   rw [hx, Port.moonlit (D-B), map_smul,map_one,light_exp,serviceP,Algebra.smul_mul_assoc,one_mul]; simp_rw [smul_smul, ←mul_pow]
   have hp: (Real.exp (-B):ℂ)*(X V).det=(X 1).det*(Real.exp (D-B):ℂ):=by rw [priceD V he,priceD 1 he]; norm_cast; rw [← Real.exp_add,← Real.exp_add]; unfold D; ring_nf
   change (((Real.exp (-B):ℂ)*_)^N) • _= _; rw [hp]; rfl
lemma brazier (he: Species S H v u t p b B X) (hg:Own f t p B' (probe v X W) A)(V:Grid f)(K:Frame f)(hp:∀ x, K ((G).embed x)=1)(N:ℕ)(y:ℝ) : tonic (O:=S) H X W N y (Lattice.gauge K V)=tonic H X W N y V:=by
   let Y:=Lattice.gauge K V; obtain ⟨a,hv,hg⟩:=hg
   have hA: foam S H X Y=foam S H X V:=by
       apply Sway.whist; obtain ⟨q,U,h⟩:= he.soapt; intro i j; rw [← h.sells,← h.sells]; apply sum_congr rfl; intro k _
       rw [(h.crop i j k).2.2.2.2.2 V K,hp,hp,show colour (1:su.El)=1 from rfl, touch_one, star_one,mul_one,one_mul]
   let M := probe v X W; have hh : alti f (M Y)= alti f (M V):=by
       refine sum_congr rfl fun i _=>?_ ; let x:=touch (colour (K i)); have hs:x ∈unitary _:= touch_u (x:=colour (K i)) ⟨su.mat_star_mul _,su.mat_mul_star _⟩
       have hp: cell (M Y) i i=x*cell (M V) i i*star x:=by
            rw [← hg.sells,← hg.sells]; rw [Matrix.mul_sum,Matrix.sum_mul]; exact sum_congr rfl (fun j _=> (hg.crop i i j).2.2.2.2.2 V K)
       change _ = (cell (M V) i i).trace.re; exact congr_arg Complex.re ((congr_arg Matrix.trace hp).trans (Port.ray_touch _ _ hs))
   rw [peaking H X W he,peaking H X W he,hh,hA]
abbrev virginR (n:Side)(N:ℕ):Rise n N Empty Empty:=⟨Empty.elim,Empty.elim,Empty.elim,Empty.elim⟩
lemma vision (v:ℝ)(i:Grid n): (virginR n N).bluff v i= if RG.flags v i=∅ then 1 else 0:=by
    unfold Rise.bluff Rise.hyp; rw [tsum_empty,exp_zero,one_mul]; unfold Rise.tint; rw [tsum_eq_single ∅]
    · by_cases he : flags v i= ∅
      · rw [if_pos he,Rise.dusk,if_pos, prod_empty,map_one]; rw [he]; exact ⟨by simp [Rise.spare],by simp [Rise.wish]⟩ -- edit
      rw [if_neg he,Rise.dusk, if_neg, map_zero]; intro h; apply he; rw [← h.2]; simp [Rise.wish]
    exact fun i hi=> (hi (Subsingleton.elim ..)).elim
open Beam Villa
variable {K':KernelChoices}{T:Tube su (Flight.visit S K' H)}
local notation "G₀"=>Flight.visit S K' H
lemma gifted (T:Tube su (G₀))(he:Species S H v u t p b B X) (R:BudgetPoint)(W:ℕ→Atom su 2)(V: Grid f)(N:ℕ)(β δ:ℝ): Emitter S H K' (virginR f N) T δ β 0 R W X V= (Pane.virgin T R β).eval V • ((X 1).det^N • light _ (exp (mica (O:=S) H X W N V))) :=by
    let M:=Pane.virgin T R β
    have hp: M.exponent V=(trimP T R δ β 0).exponent V:=rfl -- E main/root
    simp only [Emitter,vision]; unfold Rep.eval; rw [show (Pane.virgin T R β).activities.gas (Pane.virgin T R β).p V= _ from (Pane.pale_value R V).2,show (Pane.virgin T R β).exponent V= _ from hp]
    split
    next h=> rw [mul_one,streak he,mul_one]
    rw [mul_zero, mul_zero,zero_smul]; simp [Kit.sheath]
end YM.QCD.Coda
