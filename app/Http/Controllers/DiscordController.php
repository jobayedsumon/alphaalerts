<?php

namespace App\Http\Controllers;

use App\Discord;
use App\Models\DiscordUser;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use Laravel\Socialite\Facades\Socialite;
use PHPOpenSourceSaver\JWTAuth\JWTAuth;

class DiscordController extends Controller
{
    public function __construct()
    {
        $this->middleware('auth:api', ['except' => ['discordCallback']]);
        $this->middleware('web', ['only' => ['discordConnect', 'discordCallback']]);
    }

    public function discordConnect(Request $request)
    {
        session()->put('token', $request->get('token'));
        return Socialite::driver ( 'discord' )->setScopes([
            'identify' ,
            'guilds' ,
            'messages.read' ,
        ])->redirect();
    }

    public function discordCallback()
    {
        try {
            $user = Socialite::driver('discord')->user();

            $token = session()->get('token');
            $tokenParts = explode(".", $token);
            $tokenPayload = json_decode(base64_decode($tokenParts[1]));

            $discordUser = DiscordUser::where('discord_id', $user->id)->first();
            if (!isset($discordUser)) {
                $discordUser = new DiscordUser();
            }
            $discordUser->user_id = $tokenPayload->sub;
            $discordUser->discord_id = $user->getId();
            $discordUser->name = $user->getName();
            $discordUser->nickname = $user->getNickname();
            $discordUser->token = $user->token;

            $discordUser->save();

            return redirect()->to('/#/discord');
        } catch (\Exception $e) {
            return redirect()->to('/#/discord');
        }


    }

    public function discordInfo()
    {
        $user = Auth::user();
        $discordUser = DiscordUser::where('user_id', $user->id)->first();

        if ($discordUser) {
            $discordUser->servers = Discord::servers($discordUser->token);
        }

        return response()->json([
            'status' => 'success',
            'discordUser' => $discordUser,
        ]);
    }

    public function discordDisconnect()
    {
        $user = Auth::user();
        $discordUser = DiscordUser::where('user_id', $user->id)->first();
        if ($discordUser) {
            $discordUser->delete();
        }

        return response()->json([
            'status' => 'success',
        ]);
    }
}
