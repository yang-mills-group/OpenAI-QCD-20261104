import YM.Poised.Beryl
/-! # All-filter comparison. Vanishing tests upgrading scaled same-grade certificate (counts included), using literal colors/mass APIs. No discarding nonlinear Lie rows. -/
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
open PhysicalNext.JointLoad Palette Steed Beacon MultiNext.SignedSource Cruising MultiNext.SignedSource.Lyre
variable {K: KernelChoices}(P:Flight j k)(h:l.val=c.val*P.L.val)(T:Tube su (Flight.visit P K h))
variable {X:Support l}{Y:Support c}{b b':Cover} {u v L:ℕ} {τ t vo A C a :ℝ}
-- NO relatish b b' necessary algebraically
lemma shiftedX {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](f:E4→E)(h:f∈rangeLt E n)(a:Cover): (fun x:E4=>f (x-Place.seat a))∈rangeLt E n:=by simp_rw [sub_eq_add_neg]; exact band_shift h _
lemma shiftedL {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] (f:E4→E)(h:f∈rangeLt E n)(x y:E4): (fun p=> f (p+x)-f (p+y))∈ rangeLt E (n-1):=by
    cases n with
    | zero=> rw [rangeLt,Submodule.mem_bot] at h; simp only [h, Pi.zero_apply,sub_self]; exact Submodule.zero_mem _
    | succ n=> rw [show (fun p=>f (p+x)-f (p+y))=(fun p=>f (p+x)-f p)-(fun p=> f (p+y)-f p) from funext fun i=>by simp]; exact Submodule.sub_mem _ (band_step h x) (band_step h y)
variable (H:TaperHol)(J:Labels.Jet su)
abbrev echoG (l:Side) (b:Cover)(H:TaperHol)(J:Labels.Jet su)(vo:ℝ)(d n:ℕ) : Pipes.Path l (ZBand d):= (iteratedDeriv n (lode d J l b H) 0,visionS d n H.T b vo)
abbrev mintT (X:Support l)(b:Cover)(H:TaperHol)(J:Labels.Jet su)(vo:ℝ)(d n:ℕ):Pipes.Path l (ZBand d):= let t:=echoG l b H J vo d n; (Mom.screen X t.1,peel X t.2)
lemma real_at (H:TaperHol)(J:Labels.Jet su): Glazed (mintT X b H J vo d n) (echoG l b H J vo d n) X:= screen_glazed (echoG l b H J vo d n) X
variable (hΩ:Nonwrapping X (wrap l b))(hS:100≤l.val)(hT: T.R.A0=linesOf P a)(ha:0<a)(hk:4≤k)(hn:n≤d)
include hΩ hS hn
local notation "JT"=> t • J
local notation "f0"=> craftT d n (b:=b) (X:=X) (b':=b') P h T J vo t
local notation "J'"=> mintT X b H JT vo d n
local notation "s₀"=>Kit.slope P.L
lemma telling : Buoyant J' X b n:=by
    let p:= pore d JT n; let S:= poseS d n vo; have hZl:=pore_sign JT hn; refine ⟨⟨p,hZl,fun i hi=>?_⟩,S,pose_band ..,fun i hi=>?_⟩
    · have hg:= real_at (X:=X) (b:=b) (n:=n) (d:=d) (vo:=vo) H JT; exact (hg.1 _ hi).trans (lode_mem JT H b X hΩ hS i hi hn)
    rw [show asks _ i=asks (visionS (c:=l) d n H.T b vo) i from (real_at H _).2 i hi, posesS d n H.T b vo hn i, fronds H.T b hΩ hS i hi]
omit hΩ hS hn
lemma buoy_sized {n k:ℕ}[Fintype B]{A:Pipes.Path l B}(Z:Buoyant A X b n)(h:n≤k): Buoyant A X b k:=by
   obtain ⟨⟨x,hx,h1⟩,y,hy,h2⟩:= Z; exact ⟨⟨x,grows (Axis→_) (by omega) hx,h1⟩,y,grows (Flet B) (by omega) hy,h2⟩
private lemma void_zero [Fintype B](x:Pipes.Path l B)(h:Buoyant x X b 1): Glazed x 0 X:=by
   obtain ⟨⟨q,hp,h1⟩,w,hw,h2⟩:=h; rw [show 1/2=0 by rfl,rangeLt, Submodule.mem_bot] at hp; rw [show (1-1)/2=0 by rfl,rangeLt, Submodule.mem_bot] at hw; rw [hp] at h1; rw [hw] at h2; constructor; · exact h1
   intro i hi; exact (h2 i hi).trans (smul_zero _)
lemma buoy_zero [Fintype B]{n:ℕ}{F:Grid l→Lat.Fields l 6}(he:Rooted X F)(v: Fin n → Pipes.Path l B)(i:Fin n)(hp:Buoyant (v i) X b 1)(hf:ContDiffAt ℝ n (F∘increment 1) 0): iteratedFDeriv ℝ n (lotsF F) 0 v=0:=by
    let p:=Function.update v i 0; rw [melody X F he v p (fun j0=> ?_) hf]; swap
    ·  by_cases h:j0=i; · subst j0; rw [show p i=0 from update_self ..]; exact void_zero (v i) hp
       rw [show p j0=v j0 from update_of_ne h ..]; exact ⟨fun j _=>rfl,fun j _=>rfl⟩
    apply ContinuousMultilinearMap.map_coord_zero _ i (update_self ..)
variable (hΔ:d/2 ≤ j)
include hΩ hS hT ha hk hΔ hn
lemma heightsT : Buoyant (f0-(Kit.slope P.L)^n • J') X b (n-1):=by
    constructor
    · let f:= paintL b' JT n d; by_cases hv:n%2=1
      · refine ⟨0,Submodule.zero_mem _,fun i hi=> ?_⟩
        have he : f=0:=by unfold f paintL; rw [pore_blank JT hn hv]; rfl
        have hz:(J').1 i=0:= ((real_at H JT).1 _ hi).trans ((lode_mem _ H b X hΩ hS i hi hn).trans (by rw [pore_blank JT hn hv]; rfl))
        have hh : f0.1 i=0:=by change forwardG X b (applyLine _ (verdict f)) i=0; unfold forwardG; rw [Mom.screen_at,if_pos hi,he]; simp [applyLine,verdict,stream]
        change f0.1 i - s₀^n • J'.1 i = _; rw [hh,hz]; change _=(0:su.Color); simp
      obtain ⟨W,hW,hp,h⟩:=accepts_V a ha P hk (show n/2≤j by omega) f (shiftedX _ (pore_sign JT hn) b')
      have ht : W-unitStep P.L^(n/2) • f∈rangeLt _ ((n-1)/2):=grows _ (by omega) hp
      have hz : unitStep P.L^(n/2)=s₀^n:=by rw [show unitStep P.L=_ from boxed_sq P.L, ←pow_mul,show 2*(n/2)=n by omega]
      rw [hz] at ht
      let p:=pore d JT n; let v:(E4→Axis→su.Color):= fun i=> W (i+Place.seat b)-s₀^n • p i
      have hP := shiftedL p (pore_sign JT hn) (Place.seat b-Place.seat b') (0:E4); have hB : (fun i:E4=> f (i+Place.seat b)-p i)∈rangeLt _ ((n-1)/2):=by
          rw [show (fun i:E4=> f (i+Place.seat b)-p i)=(fun i:E4=>p (i+(Place.seat b-Place.seat b'))-p (i+0)) from funext fun i=> by rw [add_zero,←add_sub_assoc]]; exact grows _ (by omega) hP
      have he:v∈rangeLt _ ((n-1)/2):=by
         rw [show v=(fun i=>(W-s₀^n • f) (i+Place.seat b)) + s₀^n • (fun i:E4=>f (i+Place.seat b) - p i) from funext fun i=>by simp only [Pi.add_apply,Pi.sub_apply, Pi.smul_apply,smul_sub, v]; abel]; exact Submodule.add_mem _ (band_shift ht _) (Submodule.smul_mem _ _ hB)
      refine ⟨v,he,fun i hi=>?_⟩; have hzv: J'.1 i = p (vector (Beacon.offset b i.1)) i.2:= ((real_at H JT).1 _ hi).trans (lode_mem _ H b X hΩ hS i hi hn); change forwardG X b (applyLine _ (verdict f)) i - s₀^n • J'.1 i =_; unfold forwardG; rw [Mom.screen_at,if_pos hi,hzv,hT]; change applyLine (linesOf P a) (verdict f) (plinth b i.1) i.2 - _ = _; rw [h]; unfold verdict; rw [plinth,Place.seat_add]; rfl
    let g:=paintS b' vo n d; let f:=poseS d n vo
    by_cases hv:n%2=0∨ n<3
    · have he : f=0:=by rcases hv with h|h; exact pose_empty d vo h; have ht:= pose_band d n vo; rw [show (n-1)/2=0 from by omega,rangeLt,Submodule.mem_bot] at ht; exact ht
      have hg:g=0:=by unfold g paintS; change (fun i=>f _)=_; rw [he]; rfl
      refine ⟨0,Submodule.zero_mem _,fun i hi=>?_⟩; have hz:asks J'.2 i=frond b i • f (vector (Beacon.offset b i)):=by rw [(real_at H JT).2 _ hi]; change asks (visionS d n _ _ _) _= _; rw [posesS _ n H.T b vo hn i,fronds H.T b hΩ hS i hi]
      have hh: asks f0.2 i=0:=by change asks (hiddenS X b (serve P (g ∘ Place.seat))) i= _; unfold hiddenS; rw [invers]; rw [if_pos hi]; change ap l (plinth _ _) • serve P (g ∘ Place.seat) _ = _; rw [hg]; funext j k; simp [serve]
      rw [he] at hz; change asks f0.2 i-s₀^n • asks J'.2 i= _; rw [hh,hz]; simp
    let p:=(n-3)/2; have hy:n=3+2*p:=by unfold p; omega
    have ht:f∈ rangeLt (Flet (ZBand d)) (p+1):=by rw [show p+1=(n-1)/2 by omega]; exact pose_band ..
    have hG:g∈ rangeLt _ (p+1):=shiftedX _ ht b'
    let W:=hymn P g; have hw: W-s₀^n • g ∈ rangeLt _ p:= by have h:=hem P hk g hG; rw [← hy] at h; exact h
    have he: W ∘ Place.seat=serve P (g ∘ Place.seat):= laurel P hk g hG (by omega)
    let X':= fun i:E4=> W (i+Place.seat b)-s₀^n • f i
    have hP := shiftedL f ht (Place.seat b-Place.seat b') 0; have hB:(fun i:E4=>g (i+Place.seat b)-f i)∈rangeLt _ p:=by
       rw [show (fun i:E4=> g (i+Place.seat b)-f i)=(fun i:E4=> f (i+(Place.seat b-Place.seat b'))-f (i+0)) from funext fun i=>by rw [add_zero,← add_sub_assoc]]; exact hP
    have ha : X'∈rangeLt _ p:=by rw [show X'=(fun i=>(W-s₀^n • g) (i+Place.seat b)) + s₀^n • (fun i:E4=>g (i+Place.seat b)-f i) from funext fun i=>by simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_sub,X']; abel]; exact Submodule.add_mem _ (band_shift hw _) (Submodule.smul_mem _ _ hB)
    have hVv:(n-1-1)/2=p:=by omega
    refine ⟨X',hVv.symm ▸ ha,fun i hi=>?_⟩; have h1: asks J'.2 i=frond b i • f (vector (Beacon.offset b i)):=by rw [(real_at H _).2 _ hi]; change asks (visionS d n _ _ _) _= _; rw [posesS d n H.T b vo hn i,fronds H.T b hΩ hS i hi];
    have h2:asks f0.2 i= frond b i • W (vector (Beacon.offset b i)+Place.seat b):=by change asks (hiddenS X b (serve P (g ∘ Place.seat))) i=_; unfold hiddenS; rw [invers]; rw [if_pos hi,← he]; change _ • W (Place.seat (plinth b i))=_; rw [plinth,Place.seat_add]; rfl
    change asks f0.2 i-s₀^n • asks J'.2 i=frond b i • X' _; rw [h1,h2,smul_comm (s₀^n)]; unfold X'; rw [smul_sub]
end Chute
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Chute.heightsT
