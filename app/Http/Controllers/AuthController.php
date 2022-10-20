<?php

namespace App\Http\Controllers;

use App\Models\NotificationMethod;
use App\Notifications\EmailVerification;
use Carbon\Carbon;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\Hash;
use App\Models\User;
use Illuminate\Support\Facades\Validator;
use Illuminate\Support\Str;
use Twilio\Rest\Client;
use function MongoDB\BSON\toJSON;

class AuthController extends Controller
{
    public function __construct()
    {
        $this->middleware('auth:api', ['except' => ['login','register', 'walletConnect', 'verifyEmail']]);
    }

    public function login(Request $request)
    {
        $validator = Validator::make($request->all(), [
            'email' => 'required|string|email',
            'password' => 'required|string',
        ]);

        if ($validator->fails()) {
            return response()->json([
                'status' => 'error',
                'message' => $validator->errors()->first(),
            ]);
        }

        $credentials = $request->only('email', 'password');

        $token = Auth::attempt($credentials);
        if (!$token) {
            return response()->json([
                'status' => 'error',
                'message' => 'Invalid email or password',
            ]);
        }

        $user = Auth::user();
        return response()->json([
            'status' => 'success',
            'user' => $user->load('notificationMethod'),
            'token' => $token,
        ]);

    }

    public function register(Request $request){

        $validator = Validator::make($request->all(), [
            'name' => 'required|string|max:255',
            'email' => 'required|string|email|max:255|unique:users',
            'password' => 'required|string|min:6',
        ]);

        if ($validator->fails()) {
            return response()->json([
                'status' => 'error',
                'message' => $validator->errors()->first(),
            ]);
        }

        $user = new User();
        $user->name = $request->get('name');
        $user->email = $request->get('email');
        $user->wallet_address = $request->get('wallet_address');
        $user->password = Hash::make($request->get('password'));
        $user->is_admin = $request->get('is_admin');
        $user->save();

        Auth::login($user);
        return response()->json([
            'status' => 'success',
            'message' => 'User created successfully',
            'user' => $user->load('notificationMethod'),
        ]);
    }

    public function walletConnect(Request $request){

        $validator = Validator::make($request->all(), [
            'wallet_address' => 'required|string|max:255',
        ]);

        if ($validator->fails()) {
            return response()->json([
                'status' => 'error',
                'message' => $validator->errors()->first(),
            ]);
        }

        $user = User::updateOrCreate([
            'wallet_address' => $request->get('wallet_address'),
        ]);

        $token = Auth::login($user);
        return response()->json([
            'status' => 'success',
            'message' => 'Wallet connected successfully',
            'user' => $user->load('notificationMethod'),
            'token' => $token
        ]);
    }

    public function logout()
    {
        Auth::logout();
        return response()->json([
            'status' => 'success',
            'message' => 'Successfully logged out',
        ]);
    }

    public function refresh()
    {
        return response()->json([
            'status' => 'success',
            'user' => Auth::user(),
            'token' => Auth::refresh(),
        ]);
    }

    public function profile(Request $request)
    {
        $user = Auth::user();

        $validator = Validator::make($request->all(), [
            'name' => 'required|string|max:255',
            'email' => 'required|string|email|max:255|unique:users,email,'.$user->id,
            'country_code' => 'required|string|max:255',
            'phone_number' => 'required|string|max:255',
        ]);

        if ($validator->fails()) {
            return response()->json([
                'status' => 'error',
                'message' => $validator->errors()->first(),
            ]);
        }

        if ($user->email != $request->get('email')) {
            $user->email_verified_at = null;
        }

        if ($user->country_code != $request->get('country_code') || $user->phone_number != $request->get('phone_number')) {
            $user->phone_verified_at = null;
        }

        $user->name = $request->get('name');
        $user->email = $request->get('email');
        $user->country_code = $request->get('country_code');
        $user->phone_number = $request->get('phone_number');
        $user->save();

        $notificationMethod = NotificationMethod::where('user_id', $user->id)->first();
        if (!$notificationMethod) {
            $notificationMethod = new NotificationMethod();
            $notificationMethod->user_id = $user->id;
        }
        $notificationMethod->whatsapp = $request->get('whatsapp_notify');
        $notificationMethod->email = $request->get('email_notify');

        $notificationMethod->save();

        return response()->json([
            'status' => 'success',
            'message' => 'Profile updated successfully',
            'user' => $user->load('notificationMethod'),
        ]);
    }

    public function verificationCode(Request $request)
    {
        try{
            $user = Auth::user();
            $user->country_code = $request->get('country_code');
            $user->phone_number = $request->get('phone_number');
            $user->save();

            $phone_number = $user->country_code . $user->phone_number;

            $sid = env('TWILIO_SID');
            $token = env('TWILIO_TOKEN');
            $verification_service = env('TWILIO_VERIFICATION_SERVICE');
            $twilio = new Client($sid, $token);

            $twilio->verify->v2->services($verification_service)
                ->verifications
                ->create($phone_number, "whatsapp", ["locale" => "en"]);

            return response()->json([
                'status' => 'success',
                'message' => 'Verification code sent successfully',
            ]);

        } catch(\Exception $ex){
            return response()->json([
                'status' => 'error',
                'message' => 'Please enter correct phone number and country code.',
            ]);
        }

    }

    public function verifyPhoneNumber(Request $request)
    {
        $validator = Validator::make ( $request->all () , [
            'verification_code'        => 'required' ,
        ] );

        if ( $validator->fails () ) {
            return response ()->json ( [
                'status'  => 'error' ,
                'message' => $validator->errors()->first() ,
            ] );
        }

        try {

            $user = Auth::user ();
            $phone_number = $user->country_code . $user->phone_number;
            $code = Str::of($request->get('verification_code'))->trim();

            $sid = env('TWILIO_SID');
            $token = env('TWILIO_TOKEN');
            $twilio = new Client($sid, $token);
            $verification_service = env('TWILIO_VERIFICATION_SERVICE');

            $verification_check = $twilio->verify->v2->services ($verification_service)
                ->verificationChecks
                ->create ( [
                    "to" => $phone_number,
                    "code" => $code
                ]);

            if ( $verification_check->status == 'approved' ) {
                $user->phone_verified_at = Carbon::now();
                $user->save ();
                return response ()->json ( [
                    'status'  => 'success' ,
                    'message' => 'Phone number verified successfully.' ,
                    'user' => $user->load('notificationMethod')
                ] );
            }
            else {
                return response ()->json ( [
                    'status'  => 'error' ,
                    'message' => 'Code doesn\'t match.' ,
                ] );
            }
        }catch (\Exception $ex){
            return response ()->json ( [
                'status'  => 'error' ,
                'message' => 'Error occurred. Please try again.' ,
            ] );

        }
    }

    public function sendVerificationEmail(Request $request)
    {
        try {
            $user = Auth::user();
            $validator = Validator::make($request->all(), [
                'email' => 'required|string|email|max:255|unique:users,email,'.$user->id,
            ]);


            if ($validator->fails()) {
                return response()->json([
                    'status' => 'error',
                    'message' => $validator->errors()->first(),
                ]);
            }

            $user->email = $request->get('email');
            $user->email_verified_at = null;
            $user->save();

            $id = $user->id;
            $hash = sha1($user->email);

            $user->notify(new EmailVerification($id, $hash));

            return response()->json([
                'status' => 'success',
                'message' => 'We just sent you a verification email on '.$user->email.'. Please check your inbox (or spam) to verify your email address.',
            ]);
        } catch (\Exception $exception) {
            return response()->json([
                'status' => 'error',
                'message' => 'Could not send verification email, please try again.',
            ]);
        }
    }

    public function verifyEmail ( $id , $hash ) {
        try {
            $user = User::find($id);

            if ($user && sha1($user->email) == $hash) {
                $user->email_verified_at = Carbon::now();
                $user->save();

                return redirect('/#/profile');

            } else {
                return response()->json([
                    'status' => 'error',
                    'message' => 'Invalid verification link.',
                ]);
            }
        } catch (\Exception $exception) {
            return response()->json([
                'status' => 'error',
                'message' => 'Invalid verification link.',
            ]);
        }
    }

    public function userInfo()
    {
        $user = Auth::user();
        $user->load('notificationMethod');
        return response()->json([
            'status' => 'success',
            'user' => $user,
        ]);
    }

}
