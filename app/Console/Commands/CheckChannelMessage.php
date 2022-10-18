<?php

namespace App\Console\Commands;

use App\Discord;
use App\Helper;
use App\Models\ChannelNotification;
use App\Notifications\ChannelMessage;
use Illuminate\Console\Command;
use Illuminate\Support\Facades\Log;

class CheckChannelMessage extends Command
{
    /**
     * The name and signature of the console command.
     *
     * @var string
     */
    protected $signature = 'command:CheckChannelMessage';

    /**
     * The console command description.
     *
     * @var string
     */
    protected $description = 'Check for new messages in discord channels';

    /**
     * Create a new command instance.
     *
     * @return void
     */
    public function __construct()
    {
        parent::__construct();
    }

    /**
     * Execute the console command.
     *
     * @return int
     */
    public function handle()
    {
        $channel_notifications = ChannelNotification::all();
        foreach ($channel_notifications as $channel_notification) {
            try {
                $channel = Discord::channel($channel_notification->channel_id);

                if ($channel && isset($channel->last_message_id) && $channel->last_message_id != $channel_notification->last_message_id) {

                    $user = $channel_notification->user;
                    $notificationMethod = $user->notificationMethod;

                    if ($notificationMethod && ($notificationMethod->whatsapp || $notificationMethod->email)) {

                        $lastMessage = Discord::message($channel->id, $channel->last_message_id);
                        $channelLink = Helper::shortUrl('https://discord.com/channels/'.$channel->guild_id.'/'.$channel->id);

                        $message = 'New alert in '.$channel->name.' | '.$channel_notification->server_name.': '.@$lastMessage->content.' | Please click here to view the full message: '.$channelLink.' | Powered by Alpha Alerts';

                        if ($notificationMethod->whatsapp && $user->country_code && $user->phone_number && $user->phone_verified_at) {
                            $mobile_no = $user->country_code . $user->phone_number;
                            Helper::sendWhatsapp($mobile_no, $message);
                        }

                        if ($notificationMethod->email && $user->email && $user->email_verified_at) {

                            $data['message'] = $lastMessage->content;
                            $data['channel_name'] = $channel->name;
                            $data['server_name'] = $channel_notification->server_name;
                            $data['channel_link'] = $channelLink;

                            $user->notify(new ChannelMessage($data));
                        }
                    }

                    $channel_notification->last_message_id = $channel->last_message_id;
                    $channel_notification->save();
                }

            } catch (\Exception $ex) {
                Log::error($ex->getMessage());
            }
        }

    }
}
