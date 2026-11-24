import YM.QCD.Bay.Trove
/-! # Anti-real star plus J. No loss in absolute Pack. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bay
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Metric Set
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Strut LeafM
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {D V:Type*}[Fintype D][Fintype V][DecidableEq D][DecidableEq V]{f c: Side}{g:D→ Site f}{h:V→Site f}{δ A B t a:ℝ}{m:ℕ}
variable {s:Ratio c f}{P: Therm D s g}{Q:Therm V s h}{G:Grid f→ArrayL D V}{X:Land f D V}{Y:Pays f D V}

def moon (X:Pulse f): Pulse f:=(star X.2,star X.1)
lemma fullT (U:Grid f): moon (settled U)=settled U:=by
  unfold moon settled; apply Prod.ext; · funext i; exact star_star _
  rfl
lemma Swapped (X:Pulse f): star (Prod.swap X) = moon X:=rfl -- need NormedStar Prod
lemma duals (P Q:Pulse f): ‖moon P-moon Q‖≤‖P-Q‖ :=by
  unfold moon; rw [Prod.norm_def,Prod.norm_def]; change max ‖star P.2-star Q.2‖ ‖star P.1 -star Q.1‖ ≤ max _ _; rw [← star_sub,← star_sub,norm_star,norm_star,max_comm]; exact le_rfl
lemma lunar (hp: Pack g h δ t m G A X Y)(H:Pulse f)(hx:H∈Kingdom f δ): moon H∈ Kingdom f δ:=by
  obtain ⟨U,hU⟩:=mem_iUnion.mp hx; apply mem_iUnion.mpr; refine ⟨U,?_⟩
  rw [←fullT,mem_ball,dist_eq_norm]; rw [mem_ball,dist_eq_norm] at hU; exact (duals ..).trans_lt hU
abbrev J0 := wave g5
lemma cT: star J0=J0:= by rw [J0,wave_star,g5_star]
lemma aT:J0*J0=1:=by rw [J0,wave_mul,g5_sq,wave_one]
lemma vT: J0∈unitary _:=⟨by rw [cT,aT],by rw [cT,aT]⟩
def terraL (D: Type*)[Fintype D][DecidableEq D]:ArrayL D D:=rides (Equiv.refl _) fun _=> J0
lemma terraJ : star (terraL D)=terraL D:=by unfold terraL; rw [ride_ad]; simp only [cT]; rfl

def seed (X: Land f D V): Land f V D:= fun x y M P=>J0*star (X y x M (moon P))*J0
def foldH (X:ArrayL D V): ArrayL V D:=terraL V*Xᴴ*terraL D

lemma flock (hp: Pack g h δ t m G A X Y) : Pack h g δ t m (fun U=>foldH (G U)) A (seed X) (fun i j D=>Y j i D):=by
  constructor
  · intro x y k; obtain ⟨ha,hb,hc,hd,hf,hg⟩:= hp.crop y x k
    refine ⟨ha,fun h=>(hb h).symm,fun v hv=>?_,fun v hv=>?_,fun U V H=> ?_,fun U d=>?_⟩
    · have hm : DifferentiableAt ℂ (star ∘ X y x k ∘ star) (Prod.swap v):=by rw [show Prod.swap v=star (moon v) from (by rw [← Swapped,star_star])]; exact (hc _ (lunar hp v hv)).star_star
      unfold seed; exact (((hm.comp v (differentiableAt_snd.prodMk differentiableAt_fst)).const_mul _).mul_const _)
    · have he :‖J0‖≤1:=rotation_price vT; unfold seed; apply (norm_mul_le ..).trans; apply (mul_le_of_le_one_right (norm_nonneg _) he).trans; apply (norm_mul_le ..).trans; apply (mul_le_of_le_one_left (norm_nonneg _) he).trans; rw [norm_star]; exact hd _ (lunar hp v hv)
    · simp only [comp_apply,seed,fullT]; rw [show X _ _ k (settled U)=X _ _ k (settled V) from hf U V H]
    simp only [seed,fullT,hg,star_mul,star_star]; rw [← Matrix.mul_assoc, (interlace _ _).symm.eq]; simp only [Matrix.mul_assoc]; rw [touch_star]; rw [(interlace _ g5).eq]
  · intro i j U; rw [foldH,← terraJ (D:=D)]; unfold terraL; rw [cell_ride_right,cell_ride_left,cT,cell_flip]; simp only [seed,fullT,← Matrix.sum_mul,← Matrix.mul_sum,← star_sum,hp.sells,Equiv.refl_apply]
  · intro i; exact hp.dues i
  intro i; exact hp.spends i

lemma upright {s:Strut f}{g:Site f→ℂ}{p: Spike}(h:Warrant s g p): ∃ c:ℂ,star c*c=1 ∧∀ i, lightP s p g i * J0=c • (J0 * lightP s p g i):=by
   obtain ⟨c,hc,H⟩:= chir_line h.2; have hv : star p*g5=c • (g5*star p):=by have he:=congr_arg (·*star p) H; simpa only [Matrix.mul_assoc,h.2.unit.2,mul_one, Matrix.smul_mul] using he
   refine ⟨c,hc,fun i=>?_⟩; unfold lightP J0; rw [Matrix.smul_mul,wave_mul,hv,show wave (c • _)=_ from Matrix.smul_kronecker ..,smul_comm,Matrix.mul_smul,wave_mul]; rfl -- calc assoc
lemma clovering (R: Held s P Q X): Held s Q P (seed X):=by
 refine ⟨fun u w T hp U i j S=> ?_⟩; simp only [seed,fullT,driveD,tips,still]
 rw [R.kept u w T hp]; simp only [driveD,tips,still,star_mul,star_star]; obtain ⟨c,hc,H⟩:= upright hp; have H₂ i: J0*star (lightP (raise s u) T w i)=star c • (star (lightP (raise s u) T w i)*J0):=by have h:=congr_arg star (H i); simpa only [star_smul,star_mul,cT] using h
 rw [← mul_assoc J0 _ (_*_ ),H₂,Matrix.smul_mul,Matrix.smul_mul,mul_assoc (_*_),mul_assoc (star (X _ _ _ _)),H]; simp only [Matrix.mul_smul,smul_smul,hc,one_smul,Matrix.mul_assoc]
end YM.QCD.Bay
