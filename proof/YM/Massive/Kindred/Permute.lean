import YM.Massive.Kindred.Travel
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open ConnectedActivityE6 Pressure Pressure.Stores
open Push Push.AbsoluteSums Exterior Shell Stationary Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j j}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Rails
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q T'.top N}
open Grass


open Grass Patron
variable (A: Voice f N) (i₀:Flavor N) (T) (B: Badge P₀ τ R P o χ T U b (run S.L x) r β μ z)


local notation "δ'"=> α+(N:ℝ)*ν
open Struck Library Weft Fibre
namespace Kin
open Aperture Bank Conductor Conductor.Quant MeasureTheory Sway OrbitG
open Finset Pith Aperture
open scoped Classical
variable (s: Equiv.Perm (Flavor N))
abbrev porter (s:Equiv.Perm (Flavor N))(c:Side):= flute (Lat.Row c) (Stew.spin s)
def draw (F:Flavor N→ℝ):Flavor N→ℝ:=F ∘ s.symm
lemma porter_eq (i j:Lat.Row c)(x y:Flavor N): porter s c (i,x) (j,y) = if i=j ∧ s x=y then 1 else 0:=by
    by_cases hk:i=j<;> by_cases hp:s x=y<;>simp [porter,flute,Stew.spin,hk,hp]
lemma porter_after (i j:Lat.Row c)(x y: Flavor N)(F: Matrix (Modes c N) (Modes c N) ℂ): (star (porter s c)*F*porter s c) (i,s x) (j,s y)= F (i,x) (j,y):=by
    let M:=porter s c; let W:=star M*F; have hh:(W*M) (i,s x) (j,s y)= W (i,s x) (j,y):= by
       rw [Matrix.mul_apply,sum_eq_single (j,y)]; rotate_left
       · rintro ⟨k,l⟩ _ hk; rw [show M (k,l) _=0 from ?_,mul_zero]; exact (porter_eq s k j l _).trans (if_neg (fun h=> hk (Prod.ext h.1 (s.injective h.2))))
       · simp
       unfold M; rw [porter_eq, if_pos ⟨rfl,rfl⟩,mul_one]
    rw [hh]; unfold W; rw [Matrix.mul_apply,sum_eq_single (i,x)]; rotate_left
    · rintro ⟨k,l⟩ _ hk; rw [show star M _ (k,l)=0 from ?_, zero_mul]; rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]; unfold M; rw [porter_eq, if_neg (fun h=>hk (Prod.ext h.1 (s.injective h.2))),star_zero]
    · simp
    unfold M; rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,porter_eq, if_pos ⟨rfl,rfl⟩,star_one,one_mul]
set_option maxHeartbeats 850000 in
lemma pivotW (i:Flavor N)(X:EvenA c N)(hp: Phases X): feeF (s i) (Wheel N (Stew.spin s) c X)=feeF i X:=by
    funext (g:Lat.Row c) (h:Lat.Row c); let W:=porter s c; exact (congr_fun (congr_fun (Pith.adapted W X hp) (g,s i)) (h,s i)).trans (porter_after s g h i i (Stew.grasp X.val))
variable (u:Flavor N→ℝ)
lemma scout : Phases (ingredient c u):=by
    intro p h; unfold ingredient; rw [map_sum]; exact sum_congr rfl fun i _=> phaseLoan i.2 i.1 _ p h
lemma center : Wheel N (Stew.spin s) c (ingredient c u)=ingredient c (draw s u):=by
    apply Subtype.ext; change Kit.disguise (porter s c) (Cove.light _ (ingredient c u))=Cove.light _ (ingredient c (draw s u)); rw [panelised,panelised]; unfold disguise; rw [Grass.form_map, Matrix.transpose_transpose,← Matrix.mul_assoc]; apply congr_arg; ext ⟨i,j⟩ ⟨p,q⟩
    obtain ⟨j,rfl⟩:=s.surjective j; obtain ⟨q,rfl⟩:=s.surjective q; rw [porter_after]; rcases eq_or_ne i p with rfl|h1 <;> rcases eq_or_ne j q with rfl|h2 <;> simp [draw,Massive.Onsite.offset, *]
def race (c:Side)(N:ℕ) : (Flavor N→ℝ)→ₗ[ℝ] EvenA c N where
 toFun:= ingredient c
 map_add' x y:=by unfold ingredient; rw [← sum_add_distrib]; refine sum_congr rfl fun i _=>?_ ; change unitL i.2 (x i.2+y i.2) i.1= unitL _ _ _+unitL _ _ _; rw [Lscale,Lscale,Lscale,add_smul]
 map_smul' a x:= scaling c x a
-- transport metric.Co.P
-- transpositions guarantee span map for traceless mass directions.Identity natural real. N≥2.
variable (A: Arrow N) (M:(Flavor N→ℝ)→ₗ[ℝ](Flavor N→ℝ))
local notation "F1"=> Flavor N
lemma effects (X Y c d:Flavor N)(hp:X≠c)(he:Y≠d):∃ g:Equiv.Perm (Flavor N),g X=Y∧ g c=d:=by
    let f:=Equiv.swap X Y; have hf: f X=Y:=Equiv.swap_apply_left ..; have ht:f c≠Y:=hf ▸ (f.injective.ne hp.symm)
    let e:= Equiv.swap (f c) d; refine ⟨f.trans e,?_ , Equiv.swap_apply_left ..⟩; rw [Equiv.trans_apply,hf]; exact Equiv.swap_apply_of_ne_of_ne ht.symm he
lemma cinder (i:Flavor N)(x:ℝ): draw s (Pi.single i x)=Pi.single (s i) x:=by funext j; obtain ⟨j,rfl⟩:= s.surjective j; rcases eq_or_ne i j with rfl|hh <;> simp [draw, *, Ne.symm] -- check
variable (he:∀ (s:Equiv.Perm (Flavor N))(x:Flavor N→ℝ) (i:Flavor N), M (draw s x) (s i)=M x i)
include he
lemma orients (hh:2≤N): ∃ v:ℝ,∀ x:Flavor N→ℝ, (∑ i: Flavor N,x i)=0 → ∀ i,M x i=v*x i:=by
     let a:Flavor N:= ⟨0,by omega⟩; let b:Flavor N:=⟨1,by omega⟩; have hz:a≠b:=by simp [a,b];
     let K (i j:Flavor N):= M (Pi.single i 1) j
     have hk(i j: F1)(s:Equiv.Perm F1) : K i j= K (s i) (s j):=by unfold K; rw [← he s _ j,cinder];
     let g:= K a a; let r:= K a b; have hG i: K i i=g:=by have hp:= hk i i (Equiv.swap i a); simpa [g] using hp -- syntax let
     have hr i j (h:i≠j): K i j=r:=by obtain ⟨s,he,hv⟩:= effects i a j b h hz; unfold r; rw [hk i j s,he,hv]
     refine ⟨g-r,fun x hx i=>?_⟩
     have hp: M x i= ∑ y:Flavor N, x y*K y i:=by
        rw [show M x=∑ y:Flavor N, x y • M (Pi.single y 1) from ?_,Finset.sum_apply]; rfl
        simp_rw [← map_smul]; rw [← map_sum]; apply congr_arg; funext i; rw [Finset.sum_apply,sum_eq_single i];
        · simp [Pi.smul_apply]
        · intro j _ h; simp [h.symm]
        · simp
     rw [hp]; let C:= univ.erase i; have h:i∈ univ:=mem_univ _; have he': ∑ y∈ C,x y= -x i:=by linarith only [sum_erase_add univ x h,hx] -- let.r
     rw [← Finset.sum_erase_add univ (fun y=>x y*K y i) h]; have hh: ∑ y∈ C,x y*K y i=(-x i)*r:=by rw [←he',sum_mul]; exact sum_congr rfl fun j hj=> congr_arg _ (hr j i (ne_of_mem_erase hj))
     rw [hh,hG i]; ring
end Kin
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Kin.orients
