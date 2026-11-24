import YM.Poised.Palette
import YM.Poised.Steer
/-! # Price both cover jets.
    Nonwrap with paid projection window at chosen successor. This truncates nothing in readout of growth. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Tree RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type}{d k j n:ℕ}{c l:Side}
namespace Chute
open Pipes QCD.Kit QCD.Flume QCD.Cove QCD.Creek QCD.Loom QCD.Flume QCD.Fork QCD.Port QCD.Brick Lining Lining.Ferry
open Precision Pressure Garden Run Laurent Carrier Next.Free QCD.Kit
open PhysicalNext.JointLoad Palette Steed Beacon MultiNext.SignedSource
variable {K:KernelChoices} {S:StepData c l} {P: Flight j k}(h:l.val=c.val*P.L.val)
def plinth (b:Cover)(x:Site c):= Beacon.offset b x+b
lemma pl_sq (b:Cover)(x:Site c):wrap _ (plinth b x)=x:=by unfold plinth Beacon.offset; rw [map_add,wrap_lift,sub_add_cancel]
lemma cost_p (c:Side)(x y:Cover): separation (wrap c x) (wrap c y)≤ Laurent.size (x-y):=by rw [separation, ← map_sub]; exact within_size ..
lemma step_sway (x:Axis): Laurent.size (Lattice.step x:Cover)=1:=by
   unfold Laurent.size; rw [sum_eq_single x]; · simp
   · intro j _ h; simp [Lattice.step,h]
   simp
lemma onlyX (c:Side)(x:Cover)(hn: 2*size x < c.val): Beacon.offset 0 (wrap c x)=x:=by
    unfold Beacon.offset; rw [map_zero,sub_zero]; apply lift_eq_iff.mpr; refine ⟨rfl,fun j=>?_⟩; have hz : 2*(x j).natAbs < c.val:=by apply lt_of_le_of_lt _ hn; exact Nat.mul_le_mul_left 2 (Finset.single_le_sum (f:=fun i=>(x i).natAbs) (fun _ _=>Nat.zero_le _) (mem_univ _))
    omega
lemma sway_eq (c:Side)(b x:Cover)(hn:2*size (x-b)<c.val): plinth b (wrap c x)=x:=by
   unfold plinth Beacon.offset; rw [← map_sub]; have he:= onlyX _ _ hn; unfold Beacon.offset at he; rw [map_zero,sub_zero] at he; rw [he]; abel
abbrev visionL (b:Cover)(H:TaperHol)(Y:Support c)(v:Labels.Jet su)(n d:ℕ) : Directions su c:= Mom.screen Y (iteratedDeriv n (lode d v c b H) 0)
abbrev paintL (b:Cover)(v:Labels.Jet su)(n d:ℕ): Potential su:= fun x=>pore d v n (x-Place.seat b)
-- exposed.R valuation
variable {σ:ℝ}
structure Cruising (R:Ratio c l) (X:Support l)(Y:Support c)(b d:Cover)(u v:ℕ):Prop where
   grow : ∀ x∈X, Laurent.size (cellar R.count (plinth b x)-d) ≤ v
   unroll : 2*(v+u)<c.val
   length_c: 100 ≤ c.val
   length_l: 100 ≤ l.val
   x_safe: Nonwrapping X (wrap l b)
   y_safe: Nonwrapping Y (wrap c d)
   room : ∀ x∈X, Lattice.halo (u+1) {R.parent x} ⊆ Y
namespace Cruising
variable {R:Ratio c l} {X:Support l}{Y:Support c}{b d':Cover}{u v:ℕ}(Q:Cruising R X Y b d' u v)
variable {x:Site l}(hX:x∈X)(i:Cover)(hs:size i≤u)
abbrev gate (R:Ratio c l)(b:Cover)(x:Site l):Cover:= cellar R.count (plinth b x)
include Q hX hs
lemma launch : size (gate R b x+i-d') ≤ v+u:=by
    rw [show gate R b x+i-d'=gate R b x-d'+i by abel]; exact (size_add ..).trans (Nat.add_le_add (Q.grow _ hX) hs)
lemma in_lift : plinth d' (wrap c (gate R b x+i))=gate R b x+i:= sway_eq c d' _ (lt_of_le_of_lt (Nat.mul_le_mul_left 2 (launch Q hX i hs)) Q.unroll)
lemma nearby (w:Axis): Mom.needed Y (wrap c (gate R b x+i),w):=by
   have H(k:Cover)(ht:size k≤u+1):wrap c (gate R b x+k)∈ Y:=by
       refine Q.room _ hX (halo_spec.mpr ⟨ _, Finset.mem_singleton_self _,?_⟩); rw [separation_comm,show R.parent x=wrap c (gate R b x) from (congr_arg R.parent (pl_sq b x).symm).trans (Streets.owner R _)]; apply (cost_p ..).trans; simpa using ht
   refine ⟨H _ (by omega),?_⟩; change wrap c _+Lattice.step w ∈ Y; rw [← wrap_step c w,← map_add,add_assoc]; exact H _ ((size_add ..).trans (add_le_add hs (step_sway w).le))
omit hs
lemma ticket (w:ℕ): liftCost w (gate R b x+i-d') ≤ (1+(v:ℝ))^w * liftCost w i:=by
    rw [show gate R b x+i-d'=gate R b x-d'+i by abel]; apply (liftCost_add ..).trans (mul_le_mul_of_nonneg_right ?_ (liftCost_pos ..)); exact pow_le_pow_left₀ (by positivity) (add_le_add_right (Nat.cast_le.mpr (Q.grow _ hX)) _) _
include hs
lemma glance (H:TaperHol)(J: Labels.Jet su) (hd:n≤d):let t:= gate R b x+i
    transitL (visionL d' H Y J n d) t= verdict (paintL d' J n d) t :=by
    intro t; funext j; let w:Edge (Site c):=(wrap _ t,j); change Mom.screen Y _ w= _; rw [Mom.screen_at,if_pos (nearby Q hX i hs j),lode_mem J H d' Y Q.y_safe Q.length_c w (nearby Q hX i hs j) hd]; have he : Place.seat t-Place.seat d'= Place.seat (Beacon.offset d' (wrap c t)):=by nth_rw 1 [← show plinth d' (wrap c t)=t from in_lift Q hX i hs]; unfold plinth; rw [Place.seat_add,add_sub_cancel_right]
    change pore _ _ _ (Place.seat _) _=pore _ _ _ (Place.seat t-Place.seat d') _; rw [he]
abbrev visionS (d n:ℕ)(H:Taper)(b:Cover)(v:ℝ):VectorD (Site c) (ZBand d):= iteratedDeriv n (fun t=>woe (c:=c) H b v t d) 0
abbrev paintS (b:Cover)(v:ℝ)(n d:ℕ): E4→ Flet (ZBand d):=fun x=> poseS d n v (x-Place.seat b)
lemma spinward (d n:ℕ)(H:Taper)(r:ℝ)(hf:n ≤ d):let t:=gate R b x+i
   transitS (visionS (c:=c) d n H d' r) t= paintS d' r n d (Place.seat t):=by
    intro t; let w:= wrap c t; have he:plinth d' w=t:=in_lift Q hX i hs; have hp:Place.seat t-Place.seat d'=Place.seat (Beacon.offset d' w):=by nth_rw 1 [← he]; unfold plinth; rw [Place.seat_add,add_sub_cancel_right]
    unfold transitS paintS visionS; rw [posesS d n H d' r hf w,fronds H d' Q.y_safe Q.length_c w (nearby Q hX i hs 0).1, show frond d' w=ap c t from congr_arg _ he, smul_smul,ap_sq,hp,one_smul]; rfl -- rw change abbreviation
end Cruising
-- rates
open Cruising
lemma lode_fee (H:TaperHol)(J:Labels.Jet su)(d n:ℕ)(hn:n≤d): ∃ C:ℝ, 0≤C ∧ ∀ (θ:ℝ),0≤θ→θ ≤1 →
    (∀ (c:Side)(Y:Support c)(b x:Cover)(i:Axis), ‖transitL (visionL b H Y (θ • J) n d) x i‖ ≤ C*θ*liftCost (d*d) (x-b)) ∧
    (∀ (b x:Cover)(i:Axis), ‖verdict (paintL b (θ • J) n d) x i‖ ≤ C*θ*liftCost (d*d) (x-b)):=by
    obtain ⟨C,hC,h⟩:= Costs.tau_cost d n J hn; refine ⟨C,hC,fun θ hθ hV=>?_⟩
    have hh(c:Side)(Y:Support c)(b x:Cover)(i:Axis):‖transitL (visionL b H Y (θ • J) n d) x i‖ ≤ C*θ*liftCost (d*d) (x-b):=by
       let e:Edge (Site c):=(wrap c x,i); change ‖Mom.screen Y _ e‖≤ _; rw [Mom.screen_at]; split; · exact (h H c b θ hθ hV e).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (add_le_add_right (Nat.cast_le.mpr (cost_p ..)) _) _) (by positivity))
       rw [norm_zero]; exact mul_nonneg (by positivity) (liftCost_pos ..)
    refine ⟨hh,fun b x i=>?_⟩; let n':=100*(size (x-b)+5); let c:Side:= ⟨n', by unfold n'; omega⟩; let w:= wrap c x; let e:Edge (Site c):=(w,i); let Y:Support c:={w,w+Lattice.step i}; have hW:Mom.needed Y e:=by simp [Mom.needed,Y,e]
    have hv:100 ≤ c.val:=by change 100≤100*_; omega
    have he: Nonwrapping Y (wrap c b):=by
       intro a ha; simp only [Y,Finset.mem_insert,Finset.mem_singleton] at ha; rcases ha with h|h
       · subst a; have hp:=cost_p c x b; change 10* separation w _< 100*(size (x-b)+5); unfold w; omega
       subst a; rw [← wrap_step c i, ← map_add]; have hp:=cost_p c (x+Lattice.step i) b; have hx:=size_add (x-b) (step i); rw [show x+ step i-b=x-b+step i by abel] at hp; rw [step_sway] at hx; change 10*separation _ _<100*(size (x-b)+5); omega
    have hy:=hh c Y b x i; change ‖Mom.screen Y _ e‖≤_ at hy; rw [Mom.screen_at, if_pos hW, lode_mem _ H b Y he hv e hW hn] at hy; have h1:=sway_eq c b x (by change 2*size (x-b)<100*(size (x-b)+5); omega); have hx:Place.seat x-Place.seat b=vector (Beacon.offset b w):=by nth_rw 1 [← h1]; unfold plinth; rw [Place.seat_add,add_sub_cancel_right]; rfl
    unfold verdict paintL; rw [hx]; exact hy
lemma pose_fee (d n:ℕ)(hn:n≤d): ∃ C:ℝ,0≤C ∧∀ (r:ℝ), 0≤r →
    (∀ (H:Taper)(c:Side)(b x:Cover)(i:Pipes.Shell) (j:ZBand d), ‖transitS (visionS (c:=c) d n H b r) x i j‖ ≤ C*r*liftCost (d*d) (x-b)) ∧
    (∀ (b x:Cover)(i:Pipes.Shell)(j:ZBand d), ‖paintS b r n d (Place.seat x) i j‖ ≤ C*r*liftCost (d*d) (x-b)) :=by
    obtain ⟨A,hA,h⟩:=band_growth (pose_band d n 1)
    -- direct Glow.Est.Sp.Phi.Paint global by Period lift inside Large
    let w:= (n-1)/2
    refine ⟨A*4^w,by positivity,fun r hr=>?_⟩
    have h0(v:E4)(i:Pipes.Shell)(j:ZBand d)(x:Cover)(hx:‖v‖ ≤ 4*(size x:ℝ)): ‖poseS d n r v i j‖ ≤ A*4^w*r*liftCost (d*d) x:=by
       have he:poseS d n r v=r • poseS d n 1 v:=by funext i j; change _= r • poseS d n 1 v i j; unfold poseS; dsimp only; split <;> simp
       apply (norm_le_pi_norm ((poseS d n r v) i) j).trans ((norm_le_pi_norm (poseS d n r v) i).trans _); rw [he,norm_smul,Real.norm_of_nonneg hr]
       have hg:(1+‖v‖)^w ≤ 4^w*liftCost (d*d) x:=by
          apply le_trans (pow_le_pow_left₀ (by positivity) (show 1+‖v‖ ≤ 4*(1+size x) by linarith) w); rw [mul_pow]; have hk:w≤d:=by
           unfold w; omega
          have hd:(d:ℤ)≤(d:ℤ)*(d:ℤ):= by simpa only [pow_two] using Int.le_self_sq d -- check
          unfold liftCost; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by simp) (le_trans hk (by exact_mod_cast hd))) (by positivity)
       exact (mul_le_mul_of_nonneg_left ((h v).trans (mul_le_mul_of_nonneg_left hg hA)) hr).trans_eq (by ring)
    constructor
    · intro H c b x i j; unfold transitS visionS; let y:= wrap c x; let p:=wrap c b; rw [posesS d n H b r hn y]; simp only [Pi.smul_apply,norm_smul]; rw [ap_one,one_mul]; apply (mul_le_of_le_one_left (norm_nonneg _) (spun_pay H b y)).trans (h0 _ _ _ _ ?_); let u:=y-p; apply (shade_seat (lift u)).trans
      have hp := cost_p c x b; suffices h : size (lift u)≤4*size (x-b) by exact_mod_cast h
      refine le_trans (sum_le_sum (s:=Finset.univ) (g:=fun _=>size (x-b)) (fun i _=> (component_le u i).trans hp)) (by simp [Axis]) -- defeq
    intro b x i j; unfold paintS; have he : Place.seat x-Place.seat b= Place.seat (x-b):=by ext i; simp
    rw [he]; refine h0 _ _ _ _ ((shade_seat ..).trans (by linarith [Nat.cast_nonneg (α:=ℝ) (size (x-b))]))
end Chute
end YM.Massive.Poised
