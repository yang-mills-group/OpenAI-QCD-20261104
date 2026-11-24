import YM.QCD.Garden.Shout

/-!
# colour blind spin cells of response. normalization inherited via projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Garden
open Lat Kit Lattice Wilson Function Finset Filter Metric Tree RG Precision Bloch
open Orbit Flume Sparks Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder
open Extra Iteration Placement QCD.Free
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical Kronecker
variable {a b c f L: Side}{j k:ℕ}

lemma spin_letter (t:ℂ)(A:Spike): Lat.wave (t • A)=t • Lat.wave A:=Matrix.smul_kronecker ..

def Moon := (show Spike→ₗ[ℂ] Bundle from {toFun:=Lat.wave,map_add':=fun x y=> (wave_add ..).symm,map_smul':=spin_letter}).range
lemma moony (x:Spike): Lat.wave x ∈ Moon:=⟨x,rfl⟩
lemma moon_one : (1:Bundle)∈Moon:= wave_one ▸ moony 1
lemma moon_mul {X Y:Bundle} (hx:X∈Moon)(hy:Y∈Moon): X*Y∈Moon:=by rcases hx with ⟨A,rfl⟩; rcases hy with ⟨B,rfl⟩; change Lat.wave A *Lat.wave B∈_; rw [wave_mul]; exact moony _
lemma moon_star {X:Bundle}(hx:X∈Moon): star X∈Moon:=by obtain ⟨x,rfl⟩:=hx; change star (Lat.wave x)∈_; rw [wave_star]; exact moony _

def Sun (M : Rail a b): Prop:= ∀ x y,Run.cell M x y∈Moon
lemma Sun.mul {M:Rail a b}{N:Rail b c}(hm:Sun M)(hn:Sun N):Sun (M*N):=fun x y=>by rw [Run.cell_mul]; exact Moon.sum_mem (fun i _=>moon_mul (hm x i) (hn i y))
lemma Sun.ad {M:Rail a b}(h:Sun M):Sun Mᴴ:=fun x y=> moon_star (h y x)
lemma moon_cost (u:Para) : u.model∈Moon:=by unfold Para.model; refine Moon.add_mem (Moon.smul_mem _ moon_one) (Moon.smul_mem _ (Moon.sum_mem (fun i _=>?_))); exact Moon.smul_mem _ (moony _)
lemma Sun.purse (M : Site a→Bundle)(hp:∀ i,M i∈Moon): Sun (lined M):=by
  intro i j; have he : Run.cell (lined M) i j=if i=j then M i else 0:=by ext q s; by_cases h:i=j <;> simp [Run.cell,lined,rr,h]
  rw [he]; split_ifs; exact hp _; exact Moon.zero_mem
lemma Sun.parsus : Sun (leaf c):=by
  intro i j; have he : Run.cell (leaf c) i j=scarf j i • 1:=by ext x y; rw [Matrix.smul_apply]; rfl -- defin
  rw [he]; exact Moon.smul_mem _ moon_one
lemma Sun.city (M : Site a→Bundle)(h:∀ i, M i∈Moon):Sun (install M):= (Sun.parsus.mul (Sun.purse M h)).mul (Sun.parsus.ad)

variable (P : Flight j k)(e:f.val=c.val*P.L.val)
lemma Sun.hab : Sun (Flume.rays P e):=by
  intro i j; let r:=sliceL P e; obtain ⟨⟨x,l⟩,rfl⟩:=(tunes r P.odd).surjective j
  let V:=Run.cell (1:Sheet c) i x; let z:ℂ:= (slope r.count:ℂ)*book P (tuning x) l
  have he : Run.cell (Flume.rays P e) i (twins r x l)= z • V:=by
    ext a b; change Flume.rays P e (i,a) (twins r x l,b)=_; rw [resonate]; rfl
  have hp : V∈Moon:=by unfold V; rw [Run.cell_one]; split_ifs; exact moon_one; exact Moon.zero_mem
  change Run.cell (Flume.rays P e) i (twins r x l)∈_; rw [he]; exact Moon.smul_mem z hp
lemma Sun.campus :Sun (conn P e):=by
  have he : conn P e=leaf c * Flume.rays P e *star (leaf f):=by
    unfold Flume.rays violet; rw [← Matrix.mul_assoc,← Matrix.mul_assoc,(leaf_u _).2, Matrix.one_mul,Matrix.mul_assoc,(leaf_u _).2,Matrix.mul_one]
  exact he ▸ (Sun.parsus.mul (Sun.hab P e)).mul (Sun.parsus.ad)
lemma Sun.palette : Sun (proton P e):=by
  rw [proton,father_resp]; exact ((Sun.city _ (fun i=>moon_cost _)).mul (Sun.campus P e).ad).mul (Sun.city _ (fun i=>moon_cost _)) -- may need change

-- retain only these blocks

def harvest (X:Bundle) :Spike:=X.submatrix (fun a=>(a,(0:Hue))) (fun a=>(a,(0:Hue)))
lemma harvest_s (X:Spike): harvest (Lat.wave X)=X:=by ext i j; simp [harvest,Lat.wave]

def stampB (X:Bundle):Bundle:=Lat.wave (harvest X)
lemma harbor {X:Bundle}(h:X∈Moon):stampB X=X:=by obtain ⟨a,rfl⟩:=h; exact congr_arg Lat.wave (harvest_s a)
def stampC : Bundle→L[ℂ] Bundle:= LinearMap.toContinuousLinearMap { toFun:=stampB,map_add':=fun i j=> (wave_add ..).symm,map_smul':=fun z i=> spin_letter z _ }
end YM.QCD.Garden
