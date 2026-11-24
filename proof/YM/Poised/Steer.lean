import YM.Poised.Dart
import YM.Planned.PRIMARY_INTEGRAL_295.RollFilm
/-! # Route and replies on patches, lifted true API. Comparison on all E.Entry.Marks with late Seat -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Tree RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type}{d k j n:ℕ}{c l:Side}
namespace Steed
open Pipes QCD.Kit QCD.Flume QCD.Cove QCD.Creek QCD.Loom QCD.Flume QCD.Fork QCD.Port QCD.Brick Lining Lining.Ferry
open Precision Pressure Garden Run Laurent Carrier Next.Free QCD.Kit
open PhysicalNext.JointLoad
variable {K: KernelChoices} (P:Flight j k) (h:l.val=c.val*P.L.val) (hk:4≤k) (T:Tube su (Flight.visit P K h))
abbrev transitL (q: Directions su c):Carrier.Window su.Color:=fun x i=>q (wrap _ x,i)
lemma leans (q:Directions su c) (hT : Whole T.R.A0): transitL (Heir.route T q)=applyLine T.R.A0 (transitL q):=by
   let V:= Next.SectorChange.Flat.labels q
   have hz: transitL q=Streets.aboard su c V:= funext fun x=> funext fun i=> (congr_fun (Next.SectorChange.Flat.collected q) (wrap _ x,i)).symm
   have hu(B:Directions su c) (i:Edge (Site l)): Heir.route T B i=Streets.pledge (Heir.main T) (Next.SectorChange.Flat.labels B) (i.1,Exterior.coord i.2):=by ext j; exact (Streets.code (G:=su) (Heir.main T) _ _ _).symm
   rw [hz]; apply Eq.trans _ (Streets.street (P.visit K h).ratio T.R.A0 hT V); exact funext fun x=>funext fun i=> hu q _
variable {W:Type} [Fintype B]
def acting (v:VectorD (Site c) B): VectorD (Site l) B:= let U:Matrix _ _ ℂ:=flareV (proton P h); let V:Matrix _ _ ℂ:=v; U*V
def transitS (v: VectorD (Site c) B)(x:Cover): Flet B:= ap c x • asks v (wrap c x)
def serve (f:Cover→Flet B)(x:Cover): Flet B:=fun i j=> ∑ u:Pipes.Shell,∑' z:Cover,arch P i u x z*f (cellar P.L x+z) u j
include hk
lemma crowns (v:VectorD (Site c) B): transitS (acting P h v)= serve P (transitS v):=by
   funext x i j; unfold transitS serve acting; dsimp only; change ap l x * ((show Matrix _ _ ℂ from flareV (proton P h))*(show Matrix _ _ ℂ from v)) ((Pipes.stretch _) (_,i)) j=_; rw [Matrix.mul_apply, ← Equiv.sum_comp (Pipes.stretch (Site c)), Fintype.sum_prod_type,sum_comm,Finset.mul_sum]; refine sum_congr rfl fun s _ =>?_ ; let y:= cellar P.L x; let p:=wrap c y; let q(k: Cover):=wrap c (y+k)
   let V(a:Site c):=asks v a s j
   have hu (a: Site c): HasSum (fun z:Cover=> if p+wrap c z=a then ap l x*ap c (y+z)*arch P i s x z * V a else 0) ( (flareV (proton P h) ((Pipes.stretch _) (wrap l x,i)) ((Pipes.stretch _) (a,s)))*V a):=by
      have hx:= (show HasSum _ _ from reinsH P h x a i s hk).mul_right (V a); convert! hx using 1 <;> first | rfl | (funext z; split <;> simp [*,y])
   rw [Finset.mul_sum]; change (∑ x', ap l x * (flareV (proton P h) _ _ * V x'))= _; simp_rw [← fun (i:Site c)=> (hu i).tsum_eq,← tsum_mul_left]; rw [← Summable.tsum_finsetSum (fun i _=> (hu i).summable.mul_left _)]
   refine tsum_congr fun z=> ?_; rw [Finset.sum_eq_single (p+wrap c z)]; · rw [if_pos rfl]; change _= _*(ap c (y+z)*V _); rw [map_add,← mul_assoc,← mul_assoc,← mul_assoc, ap_sq,one_mul]; unfold p y; ring
   · intro k _ hk; rw [if_neg hk.symm, mul_zero]
   simp
-- spin exact leading. Need set calk
local notation "a!"=> (P.L.val:ℝ)⁻¹ -- parser "!"?
def hymn (Z:E4→ Flet B) (p:E4): Flet B:=fun i j=> ∑ k:Pipes.Shell,spawn (arch P i k 0) (fun x=> Z x k j) ((P.L.val:ℝ)⁻¹ • p)
private abbrev stanza (u:Pipes.Shell)(a:B):Flet B →L[ℝ]ℂ:= (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : B=>ℂ) a).comp (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _=>B→ℂ) u)
lemma laurel (f:E4→Flet B)(hf:f∈rangeLt (Flet B) n)(hn:n≤j): (hymn P f) ∘ Place.seat= serve P (f ∘ Place.seat):=by
   funext x i a; unfold hymn serve Function.comp; refine sum_congr rfl fun k _=> ?_; have ht:=roll_band P hk i k x (fun x=>f x k a) (show _ from linear_band (stanza k a) _ hf) hn; rw [←ht]; exact tsum_congr fun z=>by rw [Place.seat_add]
lemma verses (f : E4→Flet B)(hf:f∈rangeLt (Flet B) n):hymn P f∈rangeLt (Flet B) n:=by
    obtain ⟨σ,C,hσ,hC,H⟩:=archG P hk; apply vector_band; intro u; apply vector_band; intro v
    let X:=rangeLt ℂ n; have h(w:Pipes.Shell): (fun x:E4=>spawn (arch P u w 0) (fun y=>f y w v) ((P.L.val:ℝ)⁻¹ • x))∈X:= dart hσ (H _ _ _) _ _ (linear_band (stanza w v) _ hf)
    convert Submodule.sum_mem X (t:=Finset.univ) (fun i _=> h i) using 1; funext x; rw [Finset.sum_apply]; rfl
lemma hem (f : E4→Flet B)(hf:f∈rangeLt (Flet B) (n+1)): hymn P f-(Kit.slope P.L)^(3+2*n) • f∈rangeLt (Flet B) n:=by
    let Y:=Kit.slope P.L; obtain ⟨σ,C,hσ,hC,H⟩:=archG P hk; apply vector_band; intro u; apply vector_band; intro v; let s:=(P.L.val:ℝ)⁻¹
    have ht(w:Pipes.Shell):=(show (fun p:E4=>spawn (arch P u w 0) (fun y=>f y w v) (s • p)-(∑' z,arch P u w 0 z)*(s:ℂ)^n*f p w v)∈ rangeLt ℂ n from by
        have hx:= dart_sway hσ (H u w 0) (fun x=> f x w v) s (linear_band (stanza w v) _ hf); exact hx)
    convert (Submodule.sum_mem (rangeLt ℂ n) (t:=Finset.univ) (fun i _=>ht i)) using 1
    funext x; unfold hymn; rw [Finset.sum_apply,Finset.sum_sub_distrib]; simp only [Pi.smul_apply,Pi.sub_apply]; apply congr_arg; rw [Finset.sum_eq_single u]; swap; · intro i _ hi; rw [roll_pin P hk u i 0,if_neg hi.symm,zero_mul,zero_mul]
    swap; · simp
    rw [roll_pin P hk u u 0,if_pos rfl]; unfold s; rw [Complex.real_smul,lot,boxed_sq]; have he : ( (P.L.val:ℂ)⁻¹)= (((Kit.slope P.L)^2 : ℝ):ℂ):=by rw [← boxed_sq P.L]; simp
    push_cast; rw [he]; push_cast; ring
end Steed
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Steed.hem
