import YM.QCD.House.Holidays
/-! # Global lifts for charged jets. Sym flips; phases from color continuity. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Patron
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Sway OrbitG
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ}
variable {G:Grid f→Sheet f}{δ a b c' q t:ℝ}{p:Strut c}{d d':Site c→ℂ}{Z P:Spike}
section scalar
variable {B:Type*}[Fintype B][DecidableEq B]
abbrev sways (X:Matrix B B ℂ):=(Sway.OrbitG.trade X).passL
lemma leaps (X Y: Matrix B B ℂ)(v: Patio (Pairs B)): sways X (sways Y v)=sways (Y*X) v:=Subtype.ext (disguise_mul _ _ _)
lemma surfeit {X:Matrix B B ℂ}(he:X∈unitary _): Bijective (sways X) :=by
   have ht (Y:Matrix B B ℂ)(he:Y∈unitary _)(x:Patio (Pairs B)): sways Y (sways (star Y) x)=x:= Subtype.ext (discard he x.val)
   refine ⟨LeftInverse.injective (show LeftInverse (sways (star X)) (sways X) from ?_), fun v=>⟨sways (star X) v, ht _ he v⟩⟩
   intro v; have hp:= ht (star X) (Unitary.star_mem he) v; rwa [star_star] at hp
lemma newly (X:Matrix B B ℂ)(v: Dirac B): surf B (disguise X v)=disguise X (surf B v):=by
   have hh (i: Pairs B): surf B (disguise X (atom i))= disguise X (surf B (atom i)):=by
      cases i
      next i=> change surf _ (adapter _ _ (psi i))=disguise X (surf B (psi i)); rw [adapt_psi,surf_P,disguise,adapt_bar]; simp only [map_sum,map_smulₛₗ,surf_P,Matrix.star_eq_conjTranspose]; rfl
      next i=> change surf _ (adapter _ _ (bar i))=disguise X (surf B (bar i)); rw [adapt_bar,surf_M,map_neg,disguise,adapt_psi]; simp only [map_sum,map_smulₛₗ,surf_M,Matrix.star_eq_conjTranspose,Matrix.transpose_apply,Matrix.conjTranspose_apply,starRingEnd_apply,star_star,smul_neg,Finset.sum_neg_distrib]
   have he(s:List (Pairs B)): surf B (disguise X (s.map atom).prod)=disguise X (surf B (s.map atom).prod):=by
      induction s with
      | nil => simp [surf_one]
      | cons j s ih=> rw [List.map_cons,List.prod_cons,map_mul,surf_mul,surf_mul, map_mul,ih,hh]
   have hx s: surf B (disguise X (mono s))=disguise X (surf B (mono s)):=by obtain ⟨w,-,-,hw⟩:=expression s; rw [hw]; simpa using he (List.ofFn w)
   rw [← write v]; simp only [map_sum,map_smul,map_smulₛₗ,hx]
lemma novel (X : Matrix B B ℂ)(v: Patio (Pairs B)): (OrbitG.spark B).passL (sways X v)=sways X ((OrbitG.spark B).passL v):=Subtype.ext (newly X v.val)
lemma imp (X:Matrix B B ℂ)(h:X∈unitary _): Bijective ((OrbitG.dawn X).passL):=by
   let P:= (OrbitG.spark B).passL; have hp: Involutive P:=fun i=>Subtype.ext ((scud i.val).trans i.2); exact (surfeit h).comp hp.bijective
lemma choirT (X:Sheet c)(W:Matrix (Flavor N) (Flavor N) ℂ)(r:EvenA c N): sways (copies N X) (sways (flute (Lat.Row c) W) r)=sways (flute _ W) (sways (copies N X) r):=by rw [leaps,leaps]; exact congr_arg (fun s:Matrix _ _ ℂ=> sways s r) (Sway.column X W)
lemma gammaL (F:ℕ)(n:Side): idol n F∈unitary _:=copies_unitary _ _ ⟨by simp,by simp⟩ -- name
end scalar
local notation "V"=>EvenA c N
abbrev Diode (N:ℕ)(z:Strut c)(p: Spike)(y:Site c→ℂ):=sways (copies N (haze z p y))
abbrev Regal (c:Side)(N:ℕ):=(OrbitG.dawn (idol c N)).passL
def Fit (v:EvenA c N):Prop:=∀ W:Matrix (Flavor N) (Flavor N) ℂ,W∈unitary _→ sways (flute _ W) v=v
lemma dated (f:ℝ)(x:EvenA c N)(h:Fit x):Fit (f • x):=fun g hp=>Eq.trans (Loom.Fleet.eSM _ (OrbitG.phare _) ..) (congr_arg _ (h g hp))
lemma dolled (f:ℝ)(x:EvenA c N)(h: Regal c N x=x): Regal c N (f • x)=f • x:=Eq.trans (Loom.Fleet.eSM _ (OrbitG.phare _) ..) (congr_arg _ h)
lemma polarizei (v: V)(h:Fit v)(X: Sheet c): Fit (sways (copies N X) v):=by intro g hh; rw [← choirT,h g hh]
lemma polarizeg (v:V)(h: Fit v):Fit ((OrbitG.spark _).passL v):=by intro g hh; rw [← novel,h g hh]
lemma copies_skim (x:ℂ)(F:ℕ)(W:Sheet c):copies F (x • W)= x • copies F W:= Matrix.blockDiagonal_smul x _ -- sig
lemma unitaryV (x:ℂ)(T:Type*)[Fintype T][DecidableEq T](hx:star x*x=1): x • (1:Matrix T T ℂ)∈unitary _:=by
    have hv:x*star x=1:= by rw [mul_comm, hx]
    constructor <;> simp only [star_smul,star_one,Matrix.smul_mul,Matrix.mul_smul,mul_one,smul_smul,hx,hv,one_smul]
lemma facade (v: V)(h: Fit v)(x:ℂ)(X:Sheet c)(hx:star x*x=1): sways (copies N (x • X)) v= sways (copies N X) v:=by
    let P:= flute (Lat.Row c) (x • (1:Matrix (Flavor N) (Flavor N) ℂ)); have hh:P=x • 1:=by ext ⟨i,l⟩ ⟨j,b⟩; by_cases h:i=j <;> by_cases hb:l=b <;> simp [P,flute, Matrix.kronecker_apply,Matrix.one_apply,h,hb,Matrix.smul_apply]
    have hv:sways P v=v:=h _ (unitaryV x _ hx)
    rw [show copies N (x • X)=P*copies N X from ?_,← leaps,hv]
    rw [copies_skim, hh,Matrix.smul_mul,one_mul]
lemma coinT (v:V)(h:Fit v)(he: Warrant p d Z)(hv:Warrant p d' P): Diode N p Z d v=Diode N p P d' v:=by
    obtain ⟨s,hS,H⟩:= Strut.faith he hv
    apply Eq.trans _ (facade v h s (haze p P d') hS)
    apply congr_arg (fun X=> sways (copies N X) v)
    change rides _ _=s • rides _ _; rw [ride_smul]; exact congr_arg _ (funext H)
lemma gammaT (v:V)(h:Fit v)(hp:Warrant p d Z): Regal c N (Diode N p Z d v)=Diode N p Z d (Regal c N v):=by
    let Vw:= (OrbitG.spark _).passL v
    obtain ⟨x,hx,hC⟩:= upright hp
    have hh : haze p Z d*chirality c=x • (chirality c*haze p Z d):=by
       change rides (act p) (lightP p Z d) *rides (Equiv.refl (Site c)) (fun _=>J0)=x • (rides (Equiv.refl (Site c)) (fun _=>J0)* rides (act p) (lightP p Z d)); rw [ride_mul,ride_mul,ride_smul,Equiv.trans_refl,Equiv.refl_trans]; exact congr_arg _ (funext hC)
    change sways (copies N (chirality c)) ((OrbitG.spark _).passL (_))=sways _ (sways (copies N (chirality c)) Vw); unfold Diode; rw [novel,leaps,leaps,← copies_mul,← copies_mul,hh]; exact facade Vw (polarizeg v h) x _ hx -- hx syntax?
lemma gaugeS (k: Frame c)(v:V): Regal c N (sways (Lat.rotates N k) v)=sways (Lat.rotates N k) (Regal c N v):=by
    let K:= (OrbitG.spark (Modes c N)).passL; change sways (copies N (chirality c)) (K (sways (Lat.rotates N k) v))=sways _ (sways (copies N (chirality c)) (K v)); rw [show K (sways (Lat.rotates N k) v)=_ from novel _ v,leaps,leaps]; unfold Lat.rotates; rw [← copies_mul,← copies_mul]; exact congr_arg (fun x:Sheet c=> sways (copies N x) _) ((rot_spin g5 k).eq) -- syntax
lemma custodial (k:Frame c)(v:V)(hp: Warrant p d Z): sways (Lat.rotates N k) (Diode N p Z d v)= Diode N p Z d (sways (Lat.rotates N (k ∘ act p)) v):=by
    unfold Diode; rw [leaps,leaps]; unfold Lat.rotates; rw [← copies_mul, ← copies_mul]; apply congr_arg (fun S:Sheet c=> sways (copies N S) v)
    change rides (act p) (lightP p Z d) * rides (Equiv.refl (Site c)) (fun i=> touch (colour (k i))) = rides (Equiv.refl (Site c)) (fun i=> touch (colour (k (act p i)))) * rides (act p) _
    rw [ride_mul,ride_mul,Equiv.refl_trans,Equiv.trans_refl]; refine congr_arg _ (funext fun i=>?_); change (_ • wave _) * touch _=touch (colour (k (act p i)))* (_ • wave _); rw [Matrix.smul_mul,Matrix.mul_smul, (interlace ..).eq];simp
end YM.QCD.Patron
